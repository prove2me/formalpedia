-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_remark_5_4_affine
-- name    : QAlgorithms.Papers.Independent.Support50.P12.remark_5_4_affine
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:39:43.398359+00:00
-- url     : https://prove2.me/theorems/c1ebc6f3-239e-4366-a4e7-d814d6b9fa50
-- title:
--   Remark 5.4, affine case 5.4-affine
-- statement:
--   Let $\mathcal A_1\subseteq B(H_1)$ and $\mathcal A_2\subseteq B(H_2)$ be concrete unital algebras on nonzero finite-dimensional complex Hilbert spaces, and let $\Phi:\mathcal A_1\to\mathcal A_2$ be complex linear. The adjoint is for $\langle X,Y\rangle_{\rm HS}=\operatorname{Tr}X^*Y$. A substochastic map has a Schwarz-contracting adjoint; stochastic additionally means trace preserving. Let $A,B\in\mathcal A_{1,+}$. Powers are zero on kernels and traces are not normalized.
--
--   Assume $\Phi$ is substochastic, $A^0\le B^0$, and $\operatorname{Tr}\Phi(B)=\operatorname{Tr}B$. For every real $a,b$, let $f(x)=b+ax$. Then $\operatorname{Tr}\Phi(A)=\operatorname{Tr}A$ and
--
--   $$S_f(\Phi(A)\Vert\Phi(B))=b\operatorname{Tr}\Phi(B)+a\operatorname{Tr}\Phi(A)=b\operatorname{Tr}B+a\operatorname{Tr}A=S_f(A\Vert B).$$
--
--   Affine preservation is automatic and imposes no reversibility conclusion.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 25, Remark 5.4, affine case 5.4-affine

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

/-- Remark 5.4 (affine case), PDF p.25: affine equality is automatic on a supported
pair, including the displayed trace formula. No reversibility conclusion is imposed. -/
theorem remark_5_4_affine [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (Phi : MatrixMap I J)
    (hp : Substochastic A B Phi) (X Y : Mat I) (hX : X ∈ A) (hY : Y ∈ A)
    (hXp : X.PosSemidef) (hYp : Y.PosSemidef) (htr : tr (Phi Y) = tr Y)
    (hs : Supports X Y) (a b : ℝ) :
    tr (Phi X) = tr X ∧
    div (fun x => b + a * x) (Phi X) (Phi Y) = ((b * tr (Phi Y) + a * tr (Phi X) : ℝ) : EReal) ∧
    div (fun x => b + a * x) (Phi X) (Phi Y) = div (fun x => b + a * x) X Y ∧
    div (fun x => b + a * x) X Y = ((b * tr Y + a * tr X : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
