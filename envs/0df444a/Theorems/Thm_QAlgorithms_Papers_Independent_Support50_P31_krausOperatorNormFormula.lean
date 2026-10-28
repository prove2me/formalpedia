-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P31_krausOperatorNormFormula
-- name    : QAlgorithms.Papers.Independent.Support50.P31.krausOperatorNormFormula
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:27:50.652998+00:00
-- url     : https://prove2.me/theorems/2f77ac55-bdf8-4cc1-b58b-8704ab1a7c10
-- title:
--   Kraus variational formula for maximal output operator norm
-- statement:
--   Let $H$ be a nonzero finite-dimensional complex Hilbert space and let $(A_k)_{k\in K}$ be a finite Kraus family satisfying $\sum_k A_k^\ast A_k=I_H$. Set $\Phi(X)=\sum_k A_kXA_k^\ast$. With $\nu_\infty(\Phi)$ the maximum operator norm of an output density matrix and $\|\cdot\|_{\mathrm{op}}$ the Hilbert-space operator norm,
--   $$
--   \nu_\infty(\Phi)
--   =\sup_{\chi\in\mathbb C^K,\ \sum_k|\chi_k|^2=1}
--    \left\|\sum_k\chi_k A_k\right\|_{\mathrm{op}}^2.
--   $$
--   All coefficient vectors in this supremum are normalized. This real-valued variational formula expresses maximal output purity directly through the Kraus operators.
-- source:
--   On some additivity problems in quantum information theory, arXiv:math-ph/0003002v2, PDF p. 6, §3, equation (11): Kraus variational formula

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P31

noncomputable section

open Filter Asymptotics

open scoped ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P31

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten)

open QAlgorithms.Papers.Independent.Gap48.P03 (holevoQuantity)

open QAlgorithms.Papers.Independent.Claimed50.P38 (tensorSuperop)

open QAlgorithms.Papers.Independent.Dependency50.P44 (tensorChannels)

/-- PDF p.6, (11): real operator-norm formula with norm-one coefficients.
Kraus normalization rules out an empty family on a nonempty space. -/
theorem krausOperatorNormFormula {I K : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype K] [DecidableEq K] (A : K → Matrix I I ℂ) (hA : IsKrausFamily A) :
    nuP ⊤ (krausApply A) = sSup (Set.range fun z :
      {z : EuclideanSpace ℂ K // ‖z‖ = 1} => specNorm (∑ k, z.val k • A k) ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Support50.P31

end
