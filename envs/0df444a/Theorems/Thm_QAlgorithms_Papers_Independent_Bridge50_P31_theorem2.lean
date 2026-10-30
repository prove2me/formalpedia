-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P31_theorem2
-- name    : QAlgorithms.Papers.Independent.Bridge50.P31.theorem2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:44:37.318555+00:00
-- url     : https://prove2.me/theorems/01e59f35-5459-4099-a23d-7b90c418c5e3
-- title:
--   Theorem 2
-- statement:
--   Let $A\subseteq B(H)$ and $B\subseteq B(K)$ be concrete finite-dimensional unital complex $C^*$-algebras on nonzero representation spaces. Maps are complex linear, $\operatorname{Tr}$ is the unnormalized representation trace, and $T^*$ is the Hilbert–Schmidt adjoint for $\langle a,b\rangle=\operatorname{Tr}(a^*b)$. A density operator is positive with trace one. All inverses of singular positive operators below are support inverses.
--
--   The computed forward dual is $T_\rho(a)=T(\rho)^{-1/2}T(\rho^{1/2}a\rho^{1/2})T(\rho)^{-1/2}$. Write $d(\sigma,\rho)=\rho^{-1/2}\sigma\rho^{-1/2}$, $\Phi=T^*T_\rho$, and $\widetilde\Phi=T_\rho T^*$. For a map $U$, $F_U$ is its fixed-point set in its domain algebra, and $M_U$ consists of elements satisfying both $U(a^*a)=U(a)^*U(a)$ and $U(aa^*)=U(a)U(a)^*$.
--
--   Let $T$ be trace preserving, let $\rho$ be a faithful density with $\rho_0=T(\rho)>0$, and assume $T^*$ and $T_\rho$ are Schwarz. Then:
--
--   1. $F_{\widetilde\Phi}\subseteq M_{T^*}$ and $F_\Phi\subseteq M_{T_\rho}$ are subalgebras.
--   2. $T^*:F_{\widetilde\Phi}\to F_\Phi$ is a $*$-isomorphism with inverse $T_\rho$.
--   3. $F_\Phi$ is a subalgebra contained in $T^*(M_{T^*})$.
--   4. Both fixed-point algebras are invariant under the respective modular conjugations by $\rho^{it}$ and $\rho_0^{it}$, for all real $t$.
--   5. $T(F_\Phi'\cap A)\subseteq F_{\widetilde\Phi}'\cap B$.
--   6. There are $\rho_0^A\in(F_{\widetilde\Phi})_+$ and $\rho^B\in F_\Phi'\cap A_+$ such that
--   $$
--   \rho=T^*(\rho_0^A)\rho^B,\qquad\rho_0=\rho_0^A T(\rho^B),\qquad\Phi^*(\rho^B)=\rho^B.
--   $$
--   All compositions and fixed-point sets are computed from $T$ and $\rho$.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, PDF p. 8, Theorem 2

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P31

open Filter MeasureTheory Set

open scoped Matrix ComplexOrder ComplexConjugate BigOperators Topology

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE)

open QAlgorithms.Papers.Independent.Dependency50.P21
  (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports matrixCommutant)

open QAlgorithms.Papers.Independent.Support50.P12
  (Alg AlgebraDensity AlgebraExtension PositiveOnConcreteAlgebra AlgebraTracePreserving
   AlgebraKPositive AlgebraCompletelyPositive supp spec cpow quasi hull modularSpec)

open QAlgorithms.Papers.Independent.Information100.P50 (OperatorMonotone)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- PDF pp.8–9, Theorem 2: all six structure clauses for the two computed compositions. -/
theorem theorem2 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (T : MatrixMap I J)
    (hmap : AlgebraExtension A B T) (htp : AlgebraTracePreserving A T)
    (rho : Mat I) (hrho : AlgebraDensity A rho) (hfaith : rho.PosDef)
    (hout : (T rho).PosDef) (hadj : SchwarzOn B (channelAdjoint T))
    (hdual : SchwarzOn A (stateDual T rho)) :
    let F := fixedPoints A (recoveryComposite T rho)
    let G := fixedPoints B (phiTilde T rho)
    (IsStarAlgebraSet G ∧ G ⊆ algebraMultiplicativeDomain B (channelAdjoint T) ∧
      IsStarAlgebraSet F ∧ F ⊆ algebraMultiplicativeDomain A (stateDual T rho)) ∧
    StarIsoOn G F (channelAdjoint T) (stateDual T rho) ∧
    (IsStarAlgebraSet F ∧ F ⊆ channelAdjoint T '' algebraMultiplicativeDomain B (channelAdjoint T)) ∧
    (∀ t : ℝ,
      (∀ a ∈ F, cpow rho (Complex.I * (t : ℂ)) * a * cpow rho (-Complex.I * (t : ℂ)) ∈ F) ∧
      (∀ b ∈ G, cpow (T rho) (Complex.I * (t : ℂ)) * b *
        cpow (T rho) (-Complex.I * (t : ℂ)) ∈ G)) ∧
    (∀ a ∈ A, a ∈ matrixCommutant F → T a ∈ matrixCommutant G) ∧
    (∃ rho0A ∈ G, rho0A.PosSemidef ∧ ∃ rhoB ∈ A,
      rhoB.PosSemidef ∧ rhoB ∈ matrixCommutant F ∧
      channelAdjoint (recoveryComposite T rho) rhoB = rhoB ∧
      rho = channelAdjoint T rho0A * rhoB ∧ T rho = rho0A * T rhoB) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P31

end
