-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P10_asymptotic_continuity
-- name    : QAlgorithms.Papers.Independent.Gap20.P10.asymptotic_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:27:21.793071+00:00
-- url     : https://prove2.me/theorems/8562cd8f-75a7-4c83-97a8-c789a18e2602
-- title:
--   Asymptotic continuity
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero, all states are positive semidefinite with trace one, and entropies use base-two logarithms with zero eigenvalues contributing zero. Write $E_I$ for one half the infimum of the paired mutual-information increment over all normalized extensions with the required unprimed marginal and arbitrary positive finite primed dimensions.
--
--   There exist a universal constant $K>0$ and a function $r:(0,\infty)\to\mathbb R$, independent of dimensions and states, with $\lim_{\epsilon\downarrow0}r(\epsilon)=0$, such that the following holds. For arbitrary states $\rho,\sigma$ on local dimensions $a,b>0$, set $d=ab$. For every $\epsilon>0$,
--
--   $$\|\rho-\sigma\|_1\le\epsilon\ \Longrightarrow\ |E_I(\rho)-E_I(\sigma)|\le K\epsilon\log_2 d+r(\epsilon).$$
--
--   The norm is the full matrix trace norm. The source uses $O(\epsilon)$ to denote only such a dimension-independent vanishing remainder, and imposes no linear bound on it.
-- source:
--   An additive and operational entanglement measure: conditional entanglement of mutual information, arXiv:0804.3683v2, PDF p. 3, Unnumbered: asymptotic continuity

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P10

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Claimed50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, Continuity: full trace norm, joint dimension d=a*b, and a
universal constant and dimension-independent remainder tending to zero.
The source's O(epsilon) means only this limit, not a linear remainder bound. -/
theorem asymptotic_continuity :
    ∃ K : ℝ, 0 < K ∧ ∃ remainder : ℝ → ℝ,
      Filter.Tendsto remainder (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      ∀ a b : ℕ, 0 < a → 0 < b →
      ∀ rho sigma : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ,
      IsDensityMatrix rho → IsDensityMatrix sigma →
      ∀ epsilon : ℝ, 0 < epsilon → traceNorm (rho - sigma) ≤ epsilon →
        |bipartiteCemi rho - bipartiteCemi sigma| ≤
          K * epsilon * Real.logb 2 ((a : ℝ) * (b : ℝ)) + remainder epsilon := by sorry

end QAlgorithms.Papers.Independent.Gap20.P10

end
