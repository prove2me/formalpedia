-- Prove2me | Theorems.Thm_PlatformCournot_proposition_2
-- name    : PlatformCournot.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:27:52.503333+00:00
-- url     : https://prove2.me/theorems/f957b1df-7609-42eb-98d1-521e51bf8283
-- title:
--   Proposition 2 — symmetric costs: tight price of anarchy bound $1+\frac{1}{(n+1)^2-1}$
-- statement:
--   Let $n\ge 1$.
--
--   1. If $C_1=C_2=\dots=C_n$ satisfy Assumption 1, then every Nash equilibrium of the open access game $(F,Q(F\times M),\pi)$ has
--   $$\rho(F\times M,C)\ \le\ 1+\frac{1}{(n+1)^2-1}.$$
--   2. The bound is tight: if $m\ge 1$, there is a symmetric cost profile satisfying Assumption 1 whose open access game has a Nash equilibrium, and every Nash equilibrium attains $\rho(F\times M,C)=1+\frac{1}{(n+1)^2-1}$.
--
--   The bound decreases in $n$ and tends to $1$: with symmetric firms, competition drives the efficiency loss to zero. For $n=1$ it is $4/3$, the case $n=1$ of Theorem 1.
--
--   Differences from the source:
--   - encoding: firms 1, …, n and markets 1, …, m → Fin n and Fin m (0-based), supply profile q i j firm first; reason: relabelling only
--   - encoding: the unique Nash equilibrium q^NE → every Nash equilibrium q; reason: Lemma 1 makes the equilibrium unique, so a claim about every equilibrium is the claim about q^NE
--   - encoding: ρ as a real ratio with ρ := 1 when both welfares are 0 → poa in ℝ≥0∞ (x/0 = ⊤ for x > 0) and the real bound embedded by ENNReal.ofReal; reason: same values wherever the paper's ratio is defined, and no real-division junk value
--   - reading: n firms → n ≥ 1; reason: for n = 0 the printed bound has the denominator (0+1)² − 1 = 0
--   - reading: "there exists a symmetric cost profile under which the upper bound is achieved" → for m ≥ 1, a symmetric profile satisfying Assumption 1 with a Nash equilibrium, and ρ equal to the bound at every Nash equilibrium; reason: the paper's markets are nonempty (for m = 0 both welfares vanish and ρ = 1 < bound), its cost profiles satisfy Assumption 1 (p.8), and ρ is evaluated at the (unique) equilibrium
--   - generalization: m markets, with m ≥ 1 implicit → part 1 for every m in ℕ, including m = 0; reason: at m = 0 both welfares vanish and ρ = 1, below the bound; every instance with m ≥ 1 is the page's
-- source:
--   Pang, Lin, Fu, Kleeman, Bitar, Wierman, Transparency and Control in Platforms for Networked Markets, arXiv:1903.04574v3, Proposition 2, p.18 (proof in Appendix A.2, p.28)

import Mathlib
import Definitions.Def_PlatformCournot_Assumption1
import Definitions.Def_PlatformCournot_IsNash
import Definitions.Def_PlatformCournot_poa

namespace PlatformCournot

/-- **Proposition 2: tight price of anarchy bound `1 + 1/((n+1)² − 1)` for symmetric costs.**
Pang et al., arXiv:1903.04574v3, Proposition 2, p.18: "Assume that C1 = C2 = ··· = Cn. The price of
anarchy associated with the corresponding networked Cournot game (F,Q(F × M),π) is upper bounded by
ρ(F × M,C) ≤ 1 + 1/((n + 1)² − 1). Additionally, this bound is tight. That is, there exists a
symmetric cost profile under which the upper bound is achieved."

For `n ≥ 1` firms: (i) every symmetric cost profile satisfying Assumption 1 has `ρ ≤ 1 + 1/((n+1)²−1)`
at every Nash equilibrium of the open access game; (ii) if `m ≥ 1`, some symmetric cost profile
satisfying Assumption 1 has a Nash equilibrium, and `ρ` equals the bound at every one of them.

**Formalization Note** `ρ` is `poa` in `ℝ≥0∞`; the real bound is embedded with `ENNReal.ofReal`. -/
theorem proposition_2 {n m : ℕ} (D : AffineDemand m) (hn : 1 ≤ n) :
    (∀ C : Fin n → ℝ → ℝ, Assumption1 C → (∀ i i', C i = C i') →
      ∀ q, IsNash D C Set.univ q →
        poa D C q ≤ ENNReal.ofReal (1 + 1 / (((n : ℝ) + 1) ^ 2 - 1))) ∧
    (1 ≤ m → ∃ C : Fin n → ℝ → ℝ, Assumption1 C ∧ (∀ i i', C i = C i') ∧
      (∃ q, IsNash D C Set.univ q) ∧
      ∀ q, IsNash D C Set.univ q →
        poa D C q = ENNReal.ofReal (1 + 1 / (((n : ℝ) + 1) ^ 2 - 1))) := by sorry

end PlatformCournot
