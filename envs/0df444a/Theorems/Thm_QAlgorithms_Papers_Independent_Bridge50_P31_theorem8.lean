-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P31_theorem8
-- name    : QAlgorithms.Papers.Independent.Bridge50.P31.theorem8
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:55:48.183664+00:00
-- url     : https://prove2.me/theorems/19f28e43-644d-4227-a41a-b1b2704b5d13
-- title:
--   Theorem 8
-- statement:
--   Let $A\subseteq B(H)$ and $B\subseteq B(K)$ be concrete finite-dimensional unital complex $C^*$-algebras on nonzero representation spaces. Maps are complex linear, $\operatorname{Tr}$ is the unnormalized representation trace, and $T^*$ is the Hilbert–Schmidt adjoint for $\langle a,b\rangle=\operatorname{Tr}(a^*b)$. A density operator is positive with trace one. All inverses of singular positive operators below are support inverses.
--
--   Let $\mathcal S$ be a set of density operators in $A$ containing an invertible $\rho$, with $\rho_0=T(\rho)$ invertible. Assume $T^*$ and the computed map
--   $$
--   T_\rho(a)=\rho_0^{-1/2}T(\rho^{1/2}a\rho^{1/2})\rho_0^{-1/2}
--   $$
--   are unital Schwarz maps. Reversibility means that one linear map $R:B\to A$, whose adjoint is unital Schwarz, satisfies $R(T(\sigma))=\sigma$ for every $\sigma\in\mathcal S$.
--
--   For a positive symmetric operator-monotone function $f:(0,\infty)\to(0,\infty)$, put $\Delta_\rho=L_\rho R_\rho^{-1}$, $J_\rho^f=f(\Delta_\rho)R_\rho$, $\lambda_\rho^f(x,y)=\operatorname{Tr}((J_\rho^f)^{-1}(x)y)$ and $\chi^2_{1/f}(\sigma,\rho)=\lambda_\rho^f(\sigma-\rho,\sigma-\rho)$. No normalization $f(1)=1$ is imposed. The finite-parameter measure $\nu_f$ is determined by $1/f(t)=a_f+\int_{[0,\infty)}(s+t)^{-1}\,d\nu_f(s)$, with $a_f\ge0$.
--
--   Let $\operatorname{Lin}(\mathcal S)=\operatorname{span}_{\mathbb R}\{\sigma_1-\sigma_2:\sigma_1,\sigma_2\in\mathcal S\}$. The following five conditions are equivalent:
--
--   1. $T$ is reversible for $\mathcal S$.
--   2. Every monotone metric is preserved on all $x\in\operatorname{Lin}(\mathcal S)$:
--   $$
--   \lambda_\rho^f(x,x)=\lambda_{T(\rho)}^f(T(x),T(x)).
--   $$
--   3. Every corresponding chi-squared divergence is preserved for every $\sigma\in\mathcal S$.
--   4. There is one symmetric positive operator-monotone $f$, with $|\operatorname{supp}\nu_f|\ge(\dim H)^2+(\dim K)^2$, such that the equality in condition 2 holds for all $x\in\operatorname{Lin}(\mathcal S)$.
--   5. There is one such $f$ for which chi-squared equality holds for every $\sigma\in\mathcal S$.
--
--   The generator is chosen before the state or tangent vector; its measure support may be infinite.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, PDF p. 24, Theorem 8

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

/-- PDF pp.24–25, Theorem 8: all FIVE equivalences; real Lin(S), all metrics,
and a SINGLE rich generator chosen before x or sigma. Printed mu_f on p.25
is read as nu_f of 1/f, as required by Proposition 4 and the proof. -/
theorem theorem8 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (T : MatrixMap I J)
    (S : Set (Mat I)) (rho : Mat I) (h : Conditions A B T S rho) :
    List.TFAE [
      FamilyReversible A B T S,
      ∀ x ∈ familySpan S, ∀ f : ℝ → ℝ, MetricGenerator f →
        metric f rho x x = metric f (T rho) (T x) (T x),
      ∀ sigma ∈ S, ∀ f : ℝ → ℝ, MetricGenerator f →
        chiSquared f sigma rho = chiSquared f (T sigma) (T rho),
      ∃ f : ℝ → ℝ, MetricGenerator f ∧ MetricRich f (Fintype.card I ^ 2 + Fintype.card J ^ 2) ∧
        ∀ x ∈ familySpan S, metric f rho x x = metric f (T rho) (T x) (T x),
      ∃ f : ℝ → ℝ, MetricGenerator f ∧ MetricRich f (Fintype.card I ^ 2 + Fintype.card J ^ 2) ∧
        ∀ sigma ∈ S, chiSquared f sigma rho = chiSquared f (T sigma) (T rho)] := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P31

end
