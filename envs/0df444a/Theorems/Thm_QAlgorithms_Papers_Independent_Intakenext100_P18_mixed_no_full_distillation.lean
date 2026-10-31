-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P18_mixed_no_full_distillation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P18.mixed_no_full_distillation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:30:41.620103+00:00
-- url     : https://prove2.me/theorems/d8397925-01c9-48ea-aa1a-b09e0c12dc41
-- title:
--   No exact full-dimensional extraction from a mixed square resource
-- statement:
--   Let $d\ge2$ and let $\rho$ be a positive trace-one operator on $\mathbb C^d\otimes\mathbb C^d$ with matrix rank greater than one. Let $P_+$ be the normalized full-dimensional plus Bell projector. Then
--
--   $$\rho\text{ is not exactly noncollectively distillable to }P_+.$$
--
--   Concretely, there are no local contractions $A,B$ with $s=\operatorname{Tr}[(A\otimes B)\rho(A\otimes B)^\dagger]>0$ and $(A\otimes B)\rho(A\otimes B)^\dagger/s=P_+$. This uses the source's exact product-filter definition (33), so a zero-success branch is excluded. It concerns the full local dimension $d$ and leaves lower-dimensional extraction open.
-- source:
--   General teleportation channel, singlet fraction and quasi-distillation, arXiv:quant-ph/9807091v2, PDF p. 10, §VI, unnumbered corollary: no mixed d-by-d state yields an exact full-dimensional singlet

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P18

noncomputable section

open QAlgorithms MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Intakenext100.P18

open QAlgorithms.Papers.Independent.Claimed50.P28 (maximallyEntangledDensity)

open QAlgorithms.Papers.Independent.Support50.P11 (choiState teleportWeyl bellKet)

open QAlgorithms.Papers.Independent.Renew46.P40 (initialJoint)

/-- PDF p.10, corollary after Proposition 2: a mixed d-by-d state cannot
produce the exact full-dimensional plus state by a positive-success product
filter. This is the source's noncollective distillation definition (33). -/
theorem mixed_no_full_distillation (d : ℕ) (hd : 2 ≤ d)
    (rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hrho : IsDensityMatrix rho)
    (hmixed : 1 < rho.rank) :
    ¬ ExactlyDistillable rho d (by omega) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P18

end
