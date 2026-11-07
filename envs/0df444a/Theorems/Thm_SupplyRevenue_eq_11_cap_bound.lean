-- Prove2me | Theorems.Thm_SupplyRevenue_eq_11_cap_bound
-- name    : SupplyRevenue.eq_11_cap_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:48:34.643235+00:00
-- url     : https://prove2.me/theorems/b99178bf-2477-4e21-95b2-19229de4894a
-- title:
--   Display (11) and the constants of §5.1
-- statement:
--   Let $0<\delta\le 1$. A pair $(\eta,a)$ is **admissible** in two cases: $D$ is XOS, $0<\eta\le 1/2$, $a=\alpha$, and $4a\delta<\eta$; or $D\in\mathcal V_d$, $0<\eta\le 1/(2d)$, and $a=\min\{\alpha,\eta/(8\delta)\}$. Here $\alpha$ is (7) with $k=\lceil\log_2(1+256m^2/\eta)\rceil$. For admissible $(\eta,a)$ and a cap-$\delta$ source of revenue $R>0$, with $H=16mR/\delta$ splitting $R=R_{\mathrm{low}}+R_{\mathrm{high}}$,
--
--   $$\mathrm{OblivItemRev}\ge a(R_{\mathrm{low}}-R/8),\quad\mathrm{OblivItemRev}\ge 3R_{\mathrm{high}}/16,\quad \tfrac78R\le(1/a+16/3)\,\mathrm{OblivItemRev},$$
--
--   and $A_\delta\le(2/a)\,\mathrm{OblivItemRev}$. With $\eta_0$ of p.11, one has $0<\eta_0\le 1/2$ and $4\alpha\delta<\eta_0$, and
--
--   1. $2/\alpha<96$ when $\delta K\le 1$; $2/\alpha\le 32(1+6\sqrt{\delta K})$ otherwise;
--   2. for $\eta=\min\{\eta_0,1/(2d)\}$, $2/a\le\max\{96,32d\delta\}$ when $\delta K\le 1$, and $2/a\le\max\{32+192\sqrt{\delta K},32d\delta\}$ otherwise;
--   3. at the critical cap, with $\eta=1/(4K)$: $\alpha\ge 7/160$, $2/\alpha<48$, strict slack; and with $\eta$ truncated at $1/(2d)$, $1/a\le 24(1+d/K)$.
--
--   These assemble the XOS and $\mathcal V_d$ rows of the goal.
--
--   Differences from the source:
--   - reading: "a fixed residual bundle order" → any injective rank `tie : Finset (Fin m) ↪ ℕ`, one per statement; reason: R3: the order is unspecified on the page, so every statement holds for every rank
--   - reading: a source of offers → one finite mixture of offers per buyer; reason: R4: p.2 "finite-mixture approximation"; each offer gives a point of a bounded finite-dimensional set, so arbitrary laws add nothing to the supremum
--   - encoding: suprema and ratios of revenues → suprema in $\mathbb R_{\ge0}\cup\{\infty\}$, constants as `ENNReal.ofReal`; reason: R9: same values; the inequalities hold literally at zero, with no junk value
--   - reading: "For XOS let a = α and choose strict slack"; "For Vd, additionally require η ≤ 1/(2d)" → (11) for every admissible $(\eta,a)$; reason: the page's proof makes no other use of the choice of $\eta$
--   - reading: class membership of the instance → every supported type is in the class; reason: R10: unsupported types do not affect any expectation
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), §5.1, p.11, (11)

import Mathlib
import Definitions.Def_SupplyRevenue_Classes
import Definitions.Def_SupplyRevenue_CapRev
import Definitions.Def_SupplyRevenue_Revenue
import Definitions.Def_SupplyRevenue_Local

open scoped ENNReal

namespace SupplyRevenue

/-- Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
§5.1, p.11, display (11) and its constants.

Admissible `(η, a)`: for XOS, `a = α` with the strict slack `4aδ < η`; for `𝒱_d`, `η ≤ 1/(2d)` and `a = min{α, η/(8δ)}`.
For a source of revenue `R > 0`, with `H = 16mR/δ` of (2), `OblivItemRev ≥ a(R_low − R/8)`, `OblivItemRev ≥ 3R_high/16`,
`(7/8) R ≤ (1/a + 16/3) OblivItemRev`, and `A_δ ≤ (2/a) OblivItemRev`. The last clauses are the constants of p.11: the
choice `η₀`, the bounds on `2/α` and `2/a`, and those at the critical cap.

**Formalization Note** `k` of (7) under the calibration (2) is `ladderLength m η`, and `α` is `alphaOf m η`. `0 < η ≤ 1/2`
is Lemma 4.2's range; for `𝒱_d` it follows from `η ≤ 1/(2d)`. `H = 16mR/δ` is the calibration (2). -/
theorem eq_11_cap_bound {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (tie : Tie m) (D : Instance n m)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    let K : ℝ := (capK m : ℝ)
    let Admissible : ℝ → ℝ → Prop := fun η a =>
      (InstanceInClass D IsXOS ∧ 0 < η ∧ η ≤ 1 / 2 ∧ a = alphaOf m η ∧ 4 * a * δ < η) ∨
      ∃ d : ℕ, 1 ≤ d ∧ d ≤ m ∧ InstanceInClass D (InV d) ∧ 0 < η ∧ η ≤ 1 / (2 * (d : ℝ)) ∧
        a = min (alphaOf m η) (η / (8 * δ))
    (∀ η a, Admissible η a →
      (∀ σ : Source n m, FeasibleSource tie D δ σ → 0 < sourceRev tie D σ →
        let R := sourceRev tie D σ
        let H := 16 * (m : ℝ) * R / δ
        let Rlow := ∑ i, sourceStat tie (D i) (σ i) (fun s => if s ≤ H then s else 0)
        let Rhigh := ∑ i, sourceStat tie (D i) (σ i) (fun s => if H < s then s else 0)
        ENNReal.ofReal (a * (Rlow - R / 8)) ≤ oblivRev tie D ∧
        ENNReal.ofReal (3 * Rhigh / 16) ≤ oblivRev tie D ∧
        ENNReal.ofReal (7 / 8 * R) ≤ ENNReal.ofReal (1 / a + 16 / 3) * oblivRev tie D) ∧
      capRev tie D δ ≤ ENNReal.ofReal (2 / a) * oblivRev tie D) ∧
    (let η₀ := etaZero K δ;
      0 < η₀ ∧ η₀ ≤ 1 / 2 ∧ 4 * alphaOf m η₀ * δ < η₀ ∧
      (δ * K ≤ 1 → 2 / alphaOf m η₀ < 96) ∧
      (1 < δ * K → 2 / alphaOf m η₀ ≤ 32 * (1 + 6 * Real.sqrt (δ * K))) ∧
      ∀ d : ℕ, 1 ≤ d → d ≤ m →
        let η := min η₀ (1 / (2 * (d : ℝ)))
        let a := min (alphaOf m η) (η / (8 * δ))
        (δ * K ≤ 1 → 2 / a ≤ max 96 (32 * (d : ℝ) * δ)) ∧
        (1 < δ * K → 2 / a ≤ max (32 + 192 * Real.sqrt (δ * K)) (32 * (d : ℝ) * δ))) ∧
    (let η := 1 / (4 * K);
      7 / 160 ≤ alphaOf m η ∧ 2 / alphaOf m η < 48 ∧
      4 * alphaOf m η * (1 / (2 * K)) < η ∧
      ∀ d : ℕ, 1 ≤ d → d ≤ m →
        let η' := min η (1 / (2 * (d : ℝ)))
        1 / min (alphaOf m η') (η' / (8 * (1 / (2 * K)))) ≤ 24 * (1 + (d : ℝ) / K)) := by sorry

end SupplyRevenue
