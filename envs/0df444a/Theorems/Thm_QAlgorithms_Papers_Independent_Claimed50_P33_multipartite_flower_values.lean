-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P33_multipartite_flower_values
-- name    : QAlgorithms.Papers.Independent.Claimed50.P33.multipartite_flower_values
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:46:03.200073+00:00
-- url     : https://prove2.me/theorems/f226939c-8ad7-4b76-b159-43daab51c6dd
-- title:
--   §IV.G unnumbered general m-party flower formulas
-- statement:
--   For $m\ge2$ and $d\ge1$, construct the $m$-party flower state by repeating the same local $(i,j)$ pair in all $m$ parties in the normalized purification $\frac1{\sqrt{2d}}\sum_{i,j}|i,j\rangle^{\otimes m}U_j|i\rangle_X$, where $U_0=1$ and $U_1$ is the unitary discrete Fourier transform, and trace out $X$. For this state $\phi_{m,d}$,
--
--   $$E_{I_m}^q(\phi_{m,d})=m+\log_2d,\qquad E_{I_m}^c(\phi_{m,d})=m+\frac m2\log_2d,$$
--   $$E_{S_m}^q(\phi_{m,d})=E_{S_m}^c(\phi_{m,d})=m+\log_2d.$$
--
--   All values are in bits without $1/2$. At $m=2$ the two total versions agree; strict flower separation requires $m\ge3$ and $d>1$.
-- source:
--   Squashed entanglement for multipartite states and entanglement measures based on the mixed convex roof, arXiv:0704.2236v3, PDF p. 8, §IV.G unnumbered general m-party flower formulas

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section IV.G, PDF p.8, unnumbered general m-party flower formulas.
The two total versions coincide at m=2; the dual versions always coincide. -/
theorem multipartite_flower_values (m d : ℕ) (hm : 2 ≤ m) (hd : 0 < d) :
    multipartiteSquashed false .total (multipartiteFlower m d) = m + Real.logb 2 d ∧
    multipartiteSquashed true .total (multipartiteFlower m d) = m + (m : ℝ)/2 * Real.logb 2 d ∧
    multipartiteSquashed false .dual (multipartiteFlower m d) = m + Real.logb 2 d ∧
    multipartiteSquashed true .dual (multipartiteFlower m d) = m + Real.logb 2 d := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P33

end
