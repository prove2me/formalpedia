-- Prove2me | Theorems.Thm_SupplyRevenue_sr_real_certificates
-- name    : SupplyRevenue.sr_real_certificates
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:47:51.949544+00:00
-- url     : https://prove2.me/theorems/83991837-28f4-43bc-bb54-6f40f8198d58
-- title:
--   The $\mathcal S_r$ row for finite real types — regularized activation, $A_\delta\le\max\{2,4r\delta\}$ Obl and $B\le 8\max\{K,r\}$ Obl
-- statement:
--   Let $D$ be in $\mathcal S_r$, $1\le r\le m$, $\delta>0$ and $t=\min\{1,1/(2r\delta)\}$. Then $t(1-tr\delta)\ge 1/2$ if $r\delta\le 1/2$, and otherwise it equals $1/(4r\delta)$. Fix a source with caps $\delta$ and revenue $R$, and $0<\varepsilon<1$. There are positive prices $q$ on the same assortments such that on every supported type and source offer, with $X,Y$ the full-stock demands at the source and at $q$,
--
--   $$Y\subseteq X,\qquad q(Y)\ge(1-\varepsilon)p(X). \tag{5}$$
--
--   Independent whole-offer activation by $t$ then earns at least $(1-\varepsilon)t(1-tr\delta)R$ in every fixed order, with actual allocation probabilities at most $t$ times the source marginals. For positive source prices the same holds with $q=p$ and $\varepsilon=0$. Consequently
--
--   $$A_\delta\le\max\{2,4r\delta\}\,\mathrm{OblivItemRev},\qquad B\le 8\max\{K,r\}\,\mathrm{OblivItemRev}.$$
--
--   This paragraph is the whole of the third row of the goal.
--
--   Differences from the source:
--   - reading: "a fixed residual bundle order" → any injective rank `tie : Finset (Fin m) ↪ ℕ`, one per statement; reason: R3: the order is unspecified on the page, so every statement holds for every rank
--   - reading: a source of offers → one finite mixture of offers per buyer; reason: R4: p.2 "finite-mixture approximation"; each offer gives a point of a bounded finite-dimensional set, so arbitrary laws add nothing to the supremum
--   - encoding: suprema and ratios of revenues → suprema in $\mathbb R_{\ge0}\cup\{\infty\}$, constants as `ENNReal.ofReal`; reason: R9: same values; the inequalities hold literally at zero, with no junk value
--   - reading: "to arbitrary relative payment precision" → every $0<\varepsilon<1$; reason: the perturbation is chosen for each $\varepsilon$; the page lets $\varepsilon\downarrow 0$
--   - reading: cap $\delta$ → any $\delta>0$; reason: Theorem 3.1 has no upper limit on the cap, and $t$ handles large $\delta$
--   - reading: class membership of the instance → every supported type is in the class; reason: R10: unsupported types do not affect any expectation
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), §3, "Proof of Theorem 3.1 and the Sr row", p.8, (5); revenue and marginal clauses of Theorem 3.1, p.7

import Mathlib
import Definitions.Def_SupplyRevenue_Classes
import Definitions.Def_SupplyRevenue_CapRev
import Definitions.Def_SupplyRevenue_BuyMany
import Definitions.Def_SupplyRevenue_Revenue

open scoped ENNReal

namespace SupplyRevenue

/-- Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
"Proof of Theorem 3.1 and the S_r row", p.8, with (5), and the revenue and marginal clauses of Theorem 3.1, p.7, for
finite real types: for a cap-`δ` source of revenue `R`, and `t = min{1, 1/(2rδ)}`, positive prices `q` on the same
assortments satisfy (5), and whole-offer activation by `t` earns `(1−ε) t (1−trδ) R` in every order, with actual
marginals at most `t` times the source marginals. For positive source prices `q = p` and `ε = 0`. Consequently
`A_δ ≤ max{2, 4rδ} OblivItemRev` and `B ≤ 8 max{K, r} OblivItemRev`.

**Formalization Note** `t` here is the activation probability. `0 < ε < 1` is the range of the perturbation. Activation is
`Mix.activate`, and the rows are independent (`indepE`). `q i a` is the perturbed offer replacing atom `a` of `σ i`.
`Y` and `X` in (5) are the tie-ruled full-stock demands at `q` and at the source offer, on supported types. -/
theorem sr_real_certificates {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (tie : Tie m) (D : Instance n m)
    (r : ℕ) (hr1 : 1 ≤ r) (hrm : r ≤ m) (hD : InstanceInClass D (InS r)) (δ : ℝ) (hδ : 0 < δ) :
    let t : ℝ := min 1 (1 / (2 * (r : ℝ) * δ))
    ((r : ℝ) * δ ≤ 1 / 2 → 1 / 2 ≤ t * (1 - t * (r : ℝ) * δ)) ∧
    (1 / 2 < (r : ℝ) * δ → t * (1 - t * (r : ℝ) * δ) = 1 / (4 * (r : ℝ) * δ)) ∧
    (∀ σ : Source n m, FeasibleSource tie D δ σ →
      (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ q : ∀ i, Fin (σ i).N → Offer m,
        (∀ i a, (q i a).assort = ((σ i).atom a).assort ∧ ∀ j, 0 < (q i a).price j) ∧
        (∀ i a θ, 0 < (D i).mass θ →
          let Y := fullDemand tie (D i) (q i a) θ
          let X := fullDemand tie (D i) ((σ i).atom a) θ
          Y ⊆ X ∧ (1 - ε) * ((σ i).atom a).pay X ≤ (q i a).pay Y) ∧
        ∀ π : Equiv.Perm (Fin n),
          let law : Fin n → Mix (Offer m) := fun i => ((σ i).map fun a _ => q i a).activate t
          (1 - ε) * t * (1 - t * (r : ℝ) * δ) * sourceRev tie D σ ≤
            indepE law (fun P => rev tie D P π) ∧
          ∀ i j, indepE law (fun P => allocProb tie D P π i j) ≤
            t * sourceMarginal tie (D i) (σ i) j) ∧
      ((∀ i a, ∀ j ∈ ((σ i).atom a).assort, 0 < ((σ i).atom a).price j) →
        ∀ π : Equiv.Perm (Fin n),
          let law : Fin n → Mix (Offer m) := fun i => (σ i).activate t
          t * (1 - t * (r : ℝ) * δ) * sourceRev tie D σ ≤ indepE law (fun P => rev tie D P π) ∧
          ∀ i j, indepE law (fun P => allocProb tie D P π i j) ≤
            t * sourceMarginal tie (D i) (σ i) j)) ∧
    capRev tie D δ ≤ ENNReal.ofReal (max 2 (4 * (r : ℝ) * δ)) * oblivRev tie D ∧
    buyManyRev D ≤
      ENNReal.ofReal (8 * max (capK m : ℝ) (r : ℝ)) * oblivRev tie D := by sorry

end SupplyRevenue
