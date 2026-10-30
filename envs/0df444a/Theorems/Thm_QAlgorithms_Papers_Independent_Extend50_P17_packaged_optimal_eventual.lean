-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P17_packaged_optimal_eventual
-- name    : QAlgorithms.Papers.Independent.Extend50.P17.packaged_optimal_eventual
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:53:53.160881+00:00
-- url     : https://prove2.me/theorems/b20c1856-3fb2-4b24-907b-1fa7f6582f62
-- title:
--   Unnumbered eventual comparison with packaged optimal PBT
-- statement:
--   Fix an integer $k\ge1$. Let $B(N,k)=\binom Nk/\binom{N+3}k$, and for equal qubit packages define $F_{\rm pack}^{\rm OPBT}(N,k)=\cos^{2k}(\pi/(N/k+2))$. There is a threshold $N_0$, depending on $k$, such that for every $N\ge N_0$ with $k\mid N$ and $2k\le N$,
--
--   $$B(N,k)<F_{\rm pack}^{\rm OPBT}(N,k).$$
--
--   The comparison is with the stronger MPBT lower bound, not with the actual MPBT fidelity.
-- source:
--   Multiport based teleportation -- transmission of a large amount of quantum information, arXiv:2008.00856v3, PDF p. 5, Unnumbered eventual comparison with packaged optimal PBT

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P17

open Filter MeasureTheory

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

/-- PDF pp.4–5, Eq.(13): eventual comparison with the stronger MPBT lower bound.
The threshold may depend on fixed k; only physical equal packages are compared. -/
theorem packaged_optimal_eventual (k : ℕ) (hk : 1 ≤ k) :
    ∃ N0 : ℕ, ∀ N ≥ N0, k ∣ N → 2*k ≤ N →
      binomialBound 2 N k < packagedOptimalFidelity N k := by sorry

end QAlgorithms.Papers.Independent.Extend50.P17

end
