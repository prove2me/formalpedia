-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P31_proposition2
-- name    : QAlgorithms.Papers.Independent.Bridge50.P31.proposition2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:42:56.736988+00:00
-- url     : https://prove2.me/theorems/62afd4ac-7061-4dbd-ab4e-8824725e21a4
-- title:
--   Proposition 2
-- statement:
--   Let $A\subseteq B(H)$ and $B\subseteq B(K)$ be concrete finite-dimensional unital complex $C^*$-algebras on nonzero representation spaces. Maps are complex linear, $\operatorname{Tr}$ is the unnormalized representation trace, and $T^*$ is the Hilbert–Schmidt adjoint for $\langle a,b\rangle=\operatorname{Tr}(a^*b)$. A density operator is positive with trace one. All inverses of singular positive operators below are support inverses.
--
--   For a positive trace-preserving $T:A\to B$, form $T_\rho(a)=T(\rho)^{-1/2}T(\rho^{1/2}a\rho^{1/2})T(\rho)^{-1/2}$ for each faithful density $\rho$. Then
--   $$
--   \bigl(\forall\rho\text{ faithful density in }A,\ T_\rho\text{ is Schwarz}\bigr)
--   \quad\Longleftrightarrow\quad T\text{ is 2-positive}.
--   $$
--   The universal quantifier over faithful references is essential; this does not assert 2-positivity from the Schwarz property at a single reference.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, PDF p. 6, Proposition 2

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

/-- PDF p.6, Proposition 2: Schwarz duals for ALL faithful states characterize 2-positivity. -/
theorem proposition2 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (T : MatrixMap I J)
    (hmap : AlgebraExtension A B T) (hpos : PositiveOnConcreteAlgebra A T)
    (htp : AlgebraTracePreserving A T) :
    (∀ rho, AlgebraDensity A rho → rho.PosDef → SchwarzOn A (stateDual T rho)) ↔
      AlgebraKPositive A T 2 := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P31

end
