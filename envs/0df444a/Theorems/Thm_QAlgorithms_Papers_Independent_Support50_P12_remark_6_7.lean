-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_remark_6_7
-- name    : QAlgorithms.Papers.Independent.Support50.P12.remark_6_7
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:45:48.788901+00:00
-- url     : https://prove2.me/theorems/7b5bd437-a638-45ef-84eb-68e8c10d8bcd
-- title:
--   Remark 6.7
-- statement:
--   Let $\mathcal A_1\subseteq B(H_1)$ and $\mathcal A_2\subseteq B(H_2)$ be concrete unital algebras on nonzero finite-dimensional complex Hilbert spaces, and let $\Phi:\mathcal A_1\to\mathcal A_2$ be complex linear. The adjoint is for $\langle X,Y\rangle_{\rm HS}=\operatorname{Tr}X^*Y$. A substochastic map has a Schwarz-contracting adjoint; stochastic additionally means trace preserving. Let $A,B\in\mathcal A_{1,+}$. Powers are zero on kernels and traces are not normalized. Write $S_\alpha(A\Vert B)$ for the unnormalized Petz Rényi entropy, $\psi_{A,B}(\alpha)=\log\operatorname{Tr}A^\alpha B^{1-\alpha}$, $C(A\Vert B)=\sup_{0\le\alpha<1}-\psi_{A,B}(\alpha)$, and $H_r(A\Vert B)=\sup_{0\le\alpha<1}[-\alpha r-\psi_{A,B}(\alpha)]/(1-\alpha)$. Logarithms are natural and $\log0=-\infty$. The Petz map is $\Phi_B^*(Y)=B^{1/2}\Phi^*(\Phi(B)^{-1/2}Y\Phi(B)^{-1/2})B^{1/2}$.
--
--   In Theorem 5.1's supported setting, assume $\Phi$ is also two-positive. Then
--
--   $$S_\alpha(\Phi(A)\Vert\Phi(B))=S_\alpha(A\Vert B)\text{ for some }0<\alpha<1\ \Longrightarrow\ \Phi_B^*(\Phi(A))=A$$
--
--   and one stochastic map recovers both $A$ and $B$. At $\alpha=0$, the explicit pair and map of Example 6.6 have preservation without recovery. Thus the interior condition has mathematical content.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 31, Remark 6.7

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

/-- Remark 6.7, PDF p.31: interior Rényi preservation implies the Petz identity
and reversibility; zero order fails for the explicit Example 6.6 pair. -/
theorem remark_6_7 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (Phi : MatrixMap I J)
    (hp : Substochastic A B Phi) (h2 : AlgebraKPositive A Phi 2)
    (X Y : Mat I) (hX : X ∈ A) (hY : Y ∈ A) (hXp : X.PosSemidef) (hYp : Y.PosSemidef)
    (hs : Supports X Y) (htr : tr (Phi Y) = tr Y) :
    ((∃ a ∈ Ioo (0 : ℝ) 1, petzRenyi a (Phi X) (Phi Y) = petzRenyi a X Y) →
      petz Y Phi (Phi X) = X ∧ Reversible A B Phi X Y) ∧
    (petzRenyi 0 (merge exampleRho) (merge exampleSigma) = petzRenyi 0 exampleRho exampleSigma ∧
      ¬ Reversible (diagonalAlgebra (Fin 3)) (diagonalAlgebra (Fin 3)) merge exampleRho exampleSigma) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
