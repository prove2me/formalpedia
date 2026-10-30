-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P17_two_row_branching
-- name    : QAlgorithms.Papers.Independent.Extend50.P17.two_row_branching
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:02:31.42653+00:00
-- url     : https://prove2.me/theorems/4596e1b4-a278-4969-b486-09fed24c4b5c
-- title:
--   Appendix C / Eq.(67): two-row branching multiplicity
-- statement:
--   Let $m,k,r,t$ be natural numbers with $2r\le m$, $2t\le m+k$, $r\le t$, and $m-r\le m+k-t$. Let $\alpha=(m-r,r)$ and $\mu=(m+k-t,t)$ be nested two-row shapes. Let $b(\alpha,\mu)$ count sequences of $k$ single-box additions from $\alpha$ to $\mu$ for which every intermediate shape is valid. Then
--
--   $$b(\alpha,\mu)=\binom{k}{t-r}-\binom{k}{m+k-r-t+1}.$$
--
--   Binomial coefficients vanish for negative or excessive integer lower arguments. With $s=m/2-r$ and $j=(m+k)/2-t$, this is Eq. (67). The count is defined by actual valid paths, independently of the closed expression.
-- source:
--   Multiport based teleportation -- transmission of a large amount of quantum information, arXiv:2008.00856v3, PDF p. 14, Appendix C / Eq.(67): two-row branching multiplicity

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P17

open Filter MeasureTheory

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

/-- PDF pp.13–14, Eq.(67): actual valid-box-addition path count, not a definition by formula. -/
theorem two_row_branching (m k r t : ℕ) (hr : 2*r ≤ m) (ht : 2*t ≤ m+k)
    (hcontainLower : r ≤ t) (hcontainUpper : m-r ≤ m+k-t) :
    (branchingPaths m k r t : ℝ) = branchingExpression m k r t := by sorry

end QAlgorithms.Papers.Independent.Extend50.P17

end
