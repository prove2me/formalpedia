-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_lemma_3_5
-- name    : QAlgorithms.Papers.Independent.Support50.P12.lemma_3_5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:23:58.942666+00:00
-- url     : https://prove2.me/theorems/750a4920-7b7e-45a6-a20d-5c6e8484f0e2
-- title:
--   Lemma 3.5
-- statement:
--   Let $\mathcal A_1\subseteq B(H_1)$ and $\mathcal A_2\subseteq B(H_2)$ be concrete unital algebras on nonzero finite-dimensional complex Hilbert spaces, and let $\Phi:\mathcal A_1\to\mathcal A_2$ be complex linear. The adjoint is for $\langle X,Y\rangle_{\rm HS}=\operatorname{Tr}X^*Y$. A substochastic map has a Schwarz-contracting adjoint; stochastic additionally means trace preserving. Let $A,B\in\mathcal A_{1,+}$. Powers are zero on kernels and traces are not normalized.
--
--   For every positive $\Phi$,
--
--   $$\Phi(B^0AB^0)\Phi(B)^{-1}\Phi(B^0AB^0)\le\Phi(B^0AB^{-1}AB^0).$$
--
--   If $A^0\le B^0$, also $\Phi(A)\Phi(B)^{-1}\Phi(A)\le\Phi(AB^{-1}A)$. If, in addition, $\Phi$ is trace non-increasing, then
--
--   $$S_{x^2}(\Phi(A)\Vert\Phi(B))=\operatorname{Tr}\Phi(A)^2\Phi(B)^{-1}\le\operatorname{Tr}A^2B^{-1}=S_{x^2}(A\Vert B).$$
--
--   The support hypothesis applies only to the latter two assertions. These comparisons underpin general monotonicity.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 11, Lemma 3.5

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports)

open QAlgorithms.Papers.Independent.Support21.P03 (ExtendedConvex)

open QAlgorithms (spectralProjector)

open QAlgorithms.Learning (IsDistribution)

open QAlgorithms.Papers.Independent.Information100.P04 (absOp)

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

/-- Lemma 3.5, PDF p.11: unconditional compression inequality; (3.4) and (3.5)
inherit support inclusion, and only the final clause requires trace non-increase. -/
theorem lemma_3_5 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J)
    (Phi : MatrixMap I J) (hc : AlgebraExtension A B Phi) (hp : PositiveOnConcreteAlgebra A Phi)
    (X Y : Mat I) (hX : X ∈ A) (hY : Y ∈ A) (hXp : X.PosSemidef) (hYp : Y.PosSemidef) :
    LE (Phi (supp Y * X * supp Y) * supportPower (Phi Y) (-1) * Phi (supp Y * X * supp Y))
      (Phi (supp Y * X * supportPower Y (-1) * X * supp Y)) ∧
    (Supports X Y → LE (Phi X * supportPower (Phi Y) (-1) * Phi X)
      (Phi (X * supportPower Y (-1) * X))) ∧
    (Supports X Y → AlgebraTraceNonincreasing A Phi →
      div (supportScalarPower 2) (Phi X) (Phi Y) = (tr (Phi X ^ 2 * supportPower (Phi Y) (-1)) : EReal) ∧
      tr (Phi X ^ 2 * supportPower (Phi Y) (-1)) ≤ tr (X ^ 2 * supportPower Y (-1)) ∧
      (tr (X ^ 2 * supportPower Y (-1)) : EReal) = div (supportScalarPower 2) X Y) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
