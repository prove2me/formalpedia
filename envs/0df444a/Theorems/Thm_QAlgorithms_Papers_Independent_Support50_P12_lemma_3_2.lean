-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_lemma_3_2
-- name    : QAlgorithms.Papers.Independent.Support50.P12.lemma_3_2
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T19:21:31.344991+00:00
-- url     : https://prove2.me/theorems/80e9ba3d-06bd-42bc-88dd-6ecccde20e6a
-- title:
--   Lemma 3.2
-- statement:
--   Let $\mathcal A_1\subseteq B(H_1)$ and $\mathcal A_2\subseteq B(H_2)$ be concrete unital algebras on nonzero finite-dimensional complex Hilbert spaces, and let $\Phi:\mathcal A_1\to\mathcal A_2$ be complex linear. The adjoint is for $\langle X,Y\rangle_{\rm HS}=\operatorname{Tr}X^*Y$. A substochastic map has a Schwarz-contracting adjoint; stochastic additionally means trace preserving. Let $A,B\in\mathcal A_{1,+}$. Powers are zero on kernels and traces are not normalized.
--
--   Assume $\Phi$ is positive and $S:=\Phi^*(\Phi(B)^0)\le I_1$. Then $\operatorname{Tr}\Phi(B)\le\operatorname{Tr}B$, and the following five conditions are equivalent:
--
--   $$\begin{gathered}\operatorname{Tr}\Phi(B)=\operatorname{Tr}B;\\f(B)S=Sf(B)=f(B)\text{ for every complex }f\text{ on spec}(B),\ f(0)=0\text{ if needed};\\B^0\le P_{\{1\}}(S);\\\Phi\text{ preserves trace on }B^0\mathcal A_1B^0;\\\Phi_B^*(\Phi(B))=B.\end{gathered}$$
--
--   Under these conditions, every positive $A$ supported in $B$ has its trace preserved. The adjoint bound is local; global trace non-increase is not substituted for it.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 10, Lemma 3.2

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

/-- Lemma 3.2, PDF p.10: the local adjoint bound, all five equivalent criteria,
and trace preservation throughout the support corner. -/
theorem lemma_3_2 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J)
    (Phi : MatrixMap I J) (hc : AlgebraExtension A B Phi) (hp : PositiveOnConcreteAlgebra A Phi)
    (Y : Mat I) (hY : Y ∈ A) (hYp : Y.PosSemidef)
    (hb : LE (channelAdjoint Phi (supp (Phi Y))) 1) :
    let S := channelAdjoint Phi (supp (Phi Y))
    let c1 := tr (Phi Y) = tr Y
    let c2 := ∀ f : ℝ → ℂ, (0 ∈ spec Y → f 0 = 0) →
      spectralFunction f Y * S = spectralFunction f Y ∧ S * spectralFunction f Y = spectralFunction f Y
    let c3 := LE (supp Y) (spectralProjector S 1)
    let c4 := CornerTP A Phi (supp Y)
    let c5 := petz Y Phi (Phi Y) = Y
    tr (Phi Y) ≤ tr Y ∧ (c1 ↔ c2) ∧ (c2 ↔ c3) ∧ (c3 ↔ c4) ∧ (c4 ↔ c5) ∧
      (c1 → ∀ X ∈ A, X.PosSemidef → Supports X Y → tr (Phi X) = tr X) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
