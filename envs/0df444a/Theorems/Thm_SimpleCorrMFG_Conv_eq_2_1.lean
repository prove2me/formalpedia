-- Prove2me | Theorems.Thm_SimpleCorrMFG_Conv_eq_2_1
-- name    : SimpleCorrMFG.Conv.eq_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:38.502141+00:00
-- url     : https://prove2.me/theorems/61d12aba-0282-4d63-ac6c-eb3d53a92b24
-- title:
--   (2.1), p. 4 — dist of two empirical measures of the same size is at most the fraction of mismatched points
-- statement:
--   Let $S$ be a nonempty finite set, $N\ge1$, and $s_1,\dots,s_N,\tilde s_1,\dots,\tilde s_N\in S$. Let $m=\frac1N\sum_{i=1}^N\delta_{s_i}$ and $\tilde m=\frac1N\sum_{i=1}^N\delta_{\tilde s_i}$, and let $\mathrm{dist}(m,\tilde m)=\frac12\sum_{x\in S}|m(x)-\tilde m(x)|$. Then
--   $$\mathrm{dist}(m,\tilde m)\le\min_{\sigma\text{ permutation of }\{1,\dots,N\}}\frac1N\sum_{i=1}^N\mathbf 1_{s_i\neq\tilde s_{\sigma(i)}}\le\frac1N\sum_{i=1}^N\mathbf 1_{s_i\neq\tilde s_i}.$$
--
--   This elementary coupling bound controls the distance between empirical measures by the number of disagreeing coordinates. It is used to prove (6.3) and in Step Four of the proof of Theorem 6.1.
--
--   **Formalization Note** The minimum over the finite nonempty set of permutations is written as an infimum.
-- source:
--   Campi & Fischer, Correlated equilibria and mean field games: a simple model, arXiv:2004.06185v2, p. 4, (2.1)

import Mathlib
import Definitions.Def_SimpleCorrMFG_Conv_Model

namespace SimpleCorrMFG.Conv

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

/-- Inequality (2.1) (p. 4): two empirical measures of the same size `N`. -/
theorem eq_2_1 {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {N : ℕ} (hN : 0 < N)
    (s s' : Fin N → S) :
    distTV (empOn Finset.univ s) (empOn Finset.univ s') ≤
        ⨅ π : Equiv.Perm (Fin N), (1 / (N : ℝ)) * ∑ i, (if s i ≠ s' (π i) then (1 : ℝ) else 0) ∧
      (⨅ π : Equiv.Perm (Fin N), (1 / (N : ℝ)) * ∑ i, (if s i ≠ s' (π i) then (1 : ℝ) else 0)) ≤
        (1 / (N : ℝ)) * ∑ i, (if s i ≠ s' i then (1 : ℝ) else 0) := by sorry

end SimpleCorrMFG.Conv
