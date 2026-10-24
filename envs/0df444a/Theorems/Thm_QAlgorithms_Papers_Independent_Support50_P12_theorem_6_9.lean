-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_theorem_6_9
-- name    : QAlgorithms.Papers.Independent.Support50.P12.theorem_6_9
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:47:23.027084+00:00
-- url     : https://prove2.me/theorems/b99496d8-36a1-41cd-a692-7e2ffb233b10
-- title:
--   Theorem 6.9
-- statement:
--   Let $\mathcal A_1\subseteq B(H_1)$ and $\mathcal A_2\subseteq B(H_2)$ be concrete unital algebras on nonzero finite-dimensional complex Hilbert spaces, and let $\Phi:\mathcal A_1\to\mathcal A_2$ be complex linear. The adjoint is for $\langle X,Y\rangle_{\rm HS}=\operatorname{Tr}X^*Y$. A substochastic map has a Schwarz-contracting adjoint; stochastic additionally means trace preserving. Let $A,B\in\mathcal A_{1,+}$. Powers are zero on kernels and traces are not normalized. Write $S_\alpha(A\Vert B)$ for the unnormalized Petz Rényi entropy, $\psi_{A,B}(\alpha)=\log\operatorname{Tr}A^\alpha B^{1-\alpha}$, $C(A\Vert B)=\sup_{0\le\alpha<1}-\psi_{A,B}(\alpha)$, and $H_r(A\Vert B)=\sup_{0\le\alpha<1}[-\alpha r-\psi_{A,B}(\alpha)]/(1-\alpha)$. Logarithms are natural and $\log0=-\infty$. The Petz map is $\Phi_B^*(Y)=B^{1/2}\Phi^*(\Phi(B)^{-1/2}Y\Phi(B)^{-1/2})B^{1/2}$.
--
--   Assume $A^0\le B^0$, $\Phi$ is substochastic, and $\operatorname{Tr}\Phi(B)=\operatorname{Tr}B$. Either suppose preserved Chernoff distance differs from both mapped zero-order endpoint entropies, or suppose a rate $r$ strictly satisfies
--
--   $$-\psi_{\Phi(A),\Phi(B)}(1)<r<-\psi_{\Phi(A),\Phi(B)}(0)-\psi\prime_{\Phi(A),\Phi(B)}(0),\qquad H_r(\Phi(A)\Vert\Phi(B))=H_r(A\Vert B).$$
--
--   The derivative branch is interpreted on nonorthogonal outputs. Then $\Phi_B^*(\Phi(A))=A$; if $\Phi$ is two-positive, one stochastic map recovers both inputs. Both Chernoff endpoint exclusions and both open rate endpoints are retained.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 31, Theorem 6.9

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

/-- Theorem 6.9, PDF pp.31–32: BOTH excluded Chernoff endpoint values, or a
STRICT interior rate. Nonorthogonality guards the real derivative in the second branch. -/
theorem theorem_6_9 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (Phi : MatrixMap I J)
    (hp : Substochastic A B Phi) (X Y : Mat I) (hX : X ∈ A) (hY : Y ∈ A)
    (hXp : X.PosSemidef) (hYp : Y.PosSemidef) (hs : Supports X Y) (htr : tr (Phi Y) = tr Y)
    (hcriterion :
      (chernoff (Phi X) (Phi Y) ≠ petzRenyi 0 (Phi X) (Phi Y) ∧
        chernoff (Phi X) (Phi Y) ≠ petzRenyi 0 (Phi Y) (Phi X) ∧
        chernoff (Phi X) (Phi Y) = chernoff X Y) ∨
      (0 < tr (supp (Phi X) * supp (Phi Y)) ∧ ∃ r : ℝ,
        -psiReal (Phi X) (Phi Y) 1 < r ∧
        r < -psiReal (Phi X) (Phi Y) 0 - deriv (psiReal (Phi X) (Phi Y)) 0 ∧
        hoeffding (Phi X) (Phi Y) r = hoeffding X Y r)) :
    petz Y Phi (Phi X) = X ∧ (AlgebraKPositive A Phi 2 → Reversible A B Phi X Y) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
