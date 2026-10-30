-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P31_radonNikodymCharacterization
-- name    : QAlgorithms.Papers.Independent.Bridge50.P31.radonNikodymCharacterization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:02:12.493741+00:00
-- url     : https://prove2.me/theorems/e653aced-342c-4661-8461-152ecc2a9169
-- title:
--   §3.2 unnumbered: commutant derivative characterization
-- statement:
--   Let $A\subseteq B(H)$ and $B\subseteq B(K)$ be concrete finite-dimensional unital complex $C^*$-algebras on nonzero representation spaces. Maps are complex linear, $\operatorname{Tr}$ is the unnormalized representation trace, and $T^*$ is the Hilbert–Schmidt adjoint for $\langle a,b\rangle=\operatorname{Tr}(a^*b)$. A density operator is positive with trace one. All inverses of singular positive operators below are support inverses.
--
--   Let $\rho,\sigma$ be densities with $\operatorname{supp}\sigma\le p:=\operatorname{supp}\rho$. Define $d=\rho^{-1/2}\sigma\rho^{-1/2}$ and $\langle a,b\rangle_\rho=\operatorname{Tr}(a^*\rho^{1/2}b\rho^{1/2})$. Then $d$ is the unique element in $pAp$ satisfying
--   $$
--   \operatorname{Tr}(\sigma a)=\langle d,a\rangle_\rho\quad(a\in A).
--   $$
--   It is positive, and its representation operator norm is the attained smallest domination coefficient:
--   $$
--   \sigma\le\|d\|\rho,\qquad
--   \sigma\le\lambda\rho\Rightarrow\|d\|\le\lambda,\qquad
--   \|d\|\ge1,\qquad \|d\|=1\Longleftrightarrow\rho=\sigma.
--   $$
--   This characterizes the computed derivative, including its support and normalization properties.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, PDF p. 12, §3.2 unnumbered: commutant derivative characterization

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

/-- PDF p.12: the COMPUTED derivative is the unique element with the weighted
pairing; its operator norm is the attained smallest domination coefficient. -/
theorem radonNikodymCharacterization [Nonempty I] (A : Alg I) (rho sigma : Mat I)
    (hrho : AlgebraDensity A rho) (hsigma : AlgebraDensity A sigma) (hsupp : Supports sigma rho) :
    let d := derivative sigma rho
    d ∈ supportCorner A (supp rho) ∧
    (∀ a ∈ A, (sigma * a).trace = weightedPair rho d a) ∧
    (∀ e ∈ supportCorner A (supp rho), (∀ a ∈ A, (sigma * a).trace = weightedPair rho e a) → e = d) ∧
    d.PosSemidef ∧ LE sigma ((QAlgorithms.specNorm d : ℂ) • rho) ∧
    (∀ lam : ℝ, LE sigma ((lam : ℂ) • rho) → QAlgorithms.specNorm d ≤ lam) ∧
    1 ≤ QAlgorithms.specNorm d ∧ (QAlgorithms.specNorm d = 1 ↔ rho = sigma) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P31

end
