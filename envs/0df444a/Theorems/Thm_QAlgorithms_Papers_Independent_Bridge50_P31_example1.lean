-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P31_example1
-- name    : QAlgorithms.Papers.Independent.Bridge50.P31.example1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:56:31.11986+00:00
-- url     : https://prove2.me/theorems/3fbb2c20-d130-4e21-864e-e70de70425a3
-- title:
--   Example 1: one strictly operator-convex divergence is insufficient
-- statement:
--   Let $A\subseteq B(H)$ and $B\subseteq B(K)$ be concrete finite-dimensional unital complex $C^*$-algebras on nonzero representation spaces. Maps are complex linear, $\operatorname{Tr}$ is the unnormalized representation trace, and $T^*$ is the Hilbert–Schmidt adjoint for $\langle a,b\rangle=\operatorname{Tr}(a^*b)$. A density operator is positive with trace one. All inverses of singular positive operators below are support inverses.
--
--   Take $A=B(H)$, a faithful density $\sigma$, and a projection $p$ such that $\sigma p\ne p\sigma$ and $\lambda=\operatorname{Tr}(p\sigma)\ne1/2$. Let $B=C^*(p)$ and let $T:A\to B$ be the computed trace-preserving conditional expectation. Put
--   $$
--   x=(1-\lambda)p+\lambda(I-p),\quad c=\lambda(1-\lambda),\quad
--   \rho=(I-x)^{-1}\sigma x=c^{-1}x\sigma x.
--   $$
--   Then $0<\lambda<1$, $p\notin\{0,I\}$, and $\rho$ is a faithful density. Moreover $T(\rho)=(I-x)^{-1}T(\sigma)x$ and both $(L_\sigma+R_\rho)^{-1}(\rho)$ and its output analogue equal $x$. For the operator-convex generator $f(t)=(1+t)^{-1}$,
--   $$
--   S_f(T(\sigma),T(\rho))=S_f(\sigma,\rho),\qquad
--   T\text{ is not reversible for }\{\rho,\sigma\}.
--   $$
--   This is an explicit insufficiency example, rather than an assumed pair of states with the desired properties.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, PDF p. 11, Example 1: one strictly operator-convex divergence is insufficient

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

/-- PDF pp.11–12, Example 1: explicit faithful states with preserved resolvent
f-divergence and no common recovery. The inequalities on lambda are conclusions. -/
theorem example1 [Nonempty I] (sigma p : Mat I)
    (hsigma : AlgebraDensity (⊤ : Alg I) sigma) (hfaith : sigma.PosDef)
    (hpstar : p.IsHermitian) (hpidem : p * p = p)
    (hnoncomm : sigma * p ≠ p * sigma) (hlam : tr (p * sigma) ≠ 1 / 2) :
    let A : Alg I := ⊤
    let B : Alg I := StarAlgebra.adjoin ℂ ({p} : Set (Mat I))
    let T := traceConditionalExpectation A B
    let lam := tr (p * sigma)
    let x := ((1 - lam : ℝ) : ℂ) • p + (lam : ℂ) • (1 - p)
    let rho := projectionExampleReference sigma p
    0 < lam ∧ lam < 1 ∧ p ≠ 0 ∧ p ≠ 1 ∧
    AlgebraDensity A rho ∧ rho.PosDef ∧
    rho = ((lam * (1 - lam))⁻¹ : ℂ) • (x * sigma * x) ∧
    T rho = (1 - x)⁻¹ * T sigma * x ∧
    resolvent sigma rho 1 rho = x ∧ resolvent (T sigma) (T rho) 1 (T rho) = x ∧
    QAlgorithms.Papers.Independent.Support50.P12.SemidefiniteOperatorConvex (fun t => (1 + t)⁻¹) ∧
    quasi (fun t => (1 + t)⁻¹) (T sigma) (T rho) = quasi (fun t => (1 + t)⁻¹) sigma rho ∧
    ¬ FamilyReversible A B T {rho, sigma} := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P31

end
