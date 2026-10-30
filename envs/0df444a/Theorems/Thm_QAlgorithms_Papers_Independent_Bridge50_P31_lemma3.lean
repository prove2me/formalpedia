-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P31_lemma3
-- name    : QAlgorithms.Papers.Independent.Bridge50.P31.lemma3
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:39:48.056954+00:00
-- url     : https://prove2.me/theorems/b622adc8-a87a-4f74-8802-3af7378201cb
-- title:
--   Lemma 3
-- statement:
--   Let $A\subseteq B(H)$ and $B\subseteq B(K)$ be concrete finite-dimensional unital complex $C^*$-algebras on nonzero representation spaces. Maps are complex linear, $\operatorname{Tr}$ is the unnormalized representation trace, and $T^*$ is the Hilbert–Schmidt adjoint for $\langle a,b\rangle=\operatorname{Tr}(a^*b)$. A density operator is positive with trace one. All inverses of singular positive operators below are support inverses.
--
--   For arbitrary $a,b,c\in A$, with no initial positivity assumption,
--   $$
--   \begin{pmatrix}a&b\\b^*&c\end{pmatrix}\ge0
--   \quad\Longleftrightarrow\quad
--   c\ge0,\quad\operatorname{ran}(b^*)\subseteq\operatorname{ran}(c),\quad a\ge bc^+b^*.
--   $$
--   Here $c^+$ is the support inverse, and the range condition is exactly the existence of the regularized sandwich limit. This retains the singular Schur-complement criterion.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, PDF p. 4, Lemma 3

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

/-- PDF pp.4–5, Lemma 3: singular Schur complement with its necessary range guard.
The p.4 sandwich typo is read using the defining a* (c+epsilon I)^-1 a limit. -/
theorem lemma3 [Nonempty I] (A : Alg I) (a b c : Mat I)
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) :
    (Matrix.fromBlocks a b (bᴴ) c).PosSemidef ↔
      c.PosSemidef ∧ SandwichDefined c (bᴴ) ∧ LE (generalizedSandwich c (bᴴ)) a := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P31

end
