-- Prove2me | Theorems.Thm_PlatformCournot_theorem_1_open_access_poa
-- name    : PlatformCournot.theorem_1_open_access_poa
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:27:46.708618+00:00
-- url     : https://prove2.me/theorems/d2894bda-0207-48af-acde-f8b9c4d37928
-- title:
--   Theorem 1 — open access price of anarchy is at most $\frac32\bigl(1-\frac1{3n+6}\bigr)$, tight when all $\alpha_j$ are equal
-- statement:
--   Consider $n$ firms and $m$ markets with affine inverse demand $p_j(d)=\alpha_j-\beta_j d$, $\alpha_j,\beta_j>0$, and the open access networked Cournot game $(F,Q(F\times M),\pi)$, in which every firm may supply every market.
--
--   1. **Bound.** For every cost function profile $C$ satisfying Assumption 1, the game has a Nash equilibrium, and every Nash equilibrium satisfies
--   $$\rho(F\times M,C)\ \le\ \frac32\Bigl(1-\frac{1}{3n+6}\Bigr).$$
--   2. **Tightness.** If $n\ge1$, $m\ge1$ and all markets have the same maximal willingness to pay, $\alpha_1=\alpha_2=\dots=\alpha_m$, then there is a cost function profile $\bar C$ satisfying Assumption 1 whose open access game has a Nash equilibrium, and every Nash equilibrium of it attains
--   $$\rho(F\times M,\bar C)=\frac32\Bigl(1-\frac{1}{3n+6}\Bigr).$$
--
--   Here $\rho$ is the ratio of the efficient welfare $\mathrm{SW}^*(F\times M,C)$ to the welfare at equilibrium (Definition 2). The bound is $4/3$ for one firm and increases to $3/2$ as $n\to\infty$ (Corollary 1), recovering the single-market bound of Johari and Tsitsiklis (2005) for any number of markets.
--
--   Differences from the source:
--   - encoding: firms 1, …, n and markets 1, …, m → Fin n and Fin m (0-based), supply profile q i j firm first; reason: relabelling only
--   - encoding: the unique Nash equilibrium q^NE → every Nash equilibrium q; reason: Lemma 1 makes the equilibrium unique, so a claim about every equilibrium is the claim about q^NE
--   - encoding: ρ as a real ratio with ρ := 1 when both welfares are 0 → poa in ℝ≥0∞ (x/0 = ⊤ for x > 0) and the real bound embedded by ENNReal.ofReal; reason: same values wherever the paper's ratio is defined, and no real-division junk value
--   - generalization: the bound ρ(F × M,C) ≤ … → also asserts that the open access game has a Nash equilibrium; reason: the page takes existence from Lemma 1 (p.12); dropping the conjunct gives the page's bound
--   - reading: tightness for "the set of n firms" and "the set of m markets" → n ≥ 1 and m ≥ 1; reason: for m = 0 both welfares vanish and ρ = 1 by the 0/0 clause of Definition 2, below the bound; the paper's firm and market sets are nonempty
--   - reading: "there exists a cost function profile C̄ such that ρ(F × M,C̄) = …" → C̄ satisfies Assumption 1, its game has a Nash equilibrium, and ρ equals the bound at every Nash equilibrium; reason: the paper's cost function profiles satisfy Assumption 1 (p.8), and ρ(F × M,C̄) is evaluated at the game's (unique) equilibrium
--   - generalization: n firms and m markets, with n, m ≥ 1 implicit → clause (a) for every n and m in ℕ, including n = 0 and m = 0; reason: at n = 0 or m = 0 both welfares vanish and ρ = 1, below the bound; every instance with n, m ≥ 1 is the page's
-- source:
--   Pang, Lin, Fu, Kleeman, Bitar, Wierman, Transparency and Control in Platforms for Networked Markets, arXiv:1903.04574v3, Theorem 1, pp.15–16 (proof in Appendix A.3, pp.29–30)

import Mathlib
import Definitions.Def_PlatformCournot_Assumption1
import Definitions.Def_PlatformCournot_IsNash
import Definitions.Def_PlatformCournot_poa
import Definitions.Def_PlatformCournot_poaBound

namespace PlatformCournot

/-- **Theorem 1: the price of anarchy of open access is at most `(3/2)(1 − 1/(3n+6))`, tight when
all markets share one maximal willingness to pay.**
Pang et al., arXiv:1903.04574v3, Theorem 1, pp.15–16: "The worst case efficiency loss associated
with a cost function profile C and the corresponding open access networked Cournot game
(F,Q(F × M),π) is upper bounded by ρ(F × M,C) ≤ (3/2)(1 − 1/(3n + 6)). The bound is tight if all
markets are identical in terms of their maximal willingness to pay. That is, if α1 = α2 = ··· = αm,
then there exists a cost function profile C̄ such that ρ(F × M,C̄) = (3/2)(1 − 1/(3n + 6))."

(a) For every cost profile `C` satisfying Assumption 1, the open access game has a Nash equilibrium,
and every Nash equilibrium `q` has `ρ ≤ (3/2)(1 − 1/(3n+6))`.
(b) If `n ≥ 1`, `m ≥ 1` and `α₁ = ⋯ = α_m`, some cost profile `C̄` satisfying Assumption 1 has a Nash
equilibrium, and every Nash equilibrium of `C̄` has `ρ = (3/2)(1 − 1/(3n+6))`.

**Formalization Note** Firms `Fin n`, markets `Fin m`, profiles `q i j`; affine untruncated prices;
`ρ` is `poa` in `ℝ≥0∞` with the 0/0 := 1 clause, evaluated at every Nash equilibrium (unique by
Lemma 1). -/
theorem theorem_1_open_access_poa {n m : ℕ} (D : AffineDemand m) :
    (∀ C : Fin n → ℝ → ℝ, Assumption1 C →
      (∃ q, IsNash D C Set.univ q) ∧
        ∀ q, IsNash D C Set.univ q → poa D C q ≤ ENNReal.ofReal (poaBound n)) ∧
    (1 ≤ n → 1 ≤ m → (∀ j j', D.α j = D.α j') →
      ∃ C : Fin n → ℝ → ℝ, Assumption1 C ∧ (∃ q, IsNash D C Set.univ q) ∧
        ∀ q, IsNash D C Set.univ q → poa D C q = ENNReal.ofReal (poaBound n)) := by sorry

end PlatformCournot
