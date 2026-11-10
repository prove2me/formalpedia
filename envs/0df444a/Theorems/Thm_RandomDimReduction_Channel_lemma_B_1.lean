-- Prove2me | Theorems.Thm_RandomDimReduction_Channel_lemma_B_1
-- name    : RandomDimReduction.Channel.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:23:50.50626+00:00
-- url     : https://prove2.me/theorems/bd336f71-20bc-4f93-932c-3e7bd9a715c6
-- title:
--   Lemma B.1 — cyclicity of the partial trace
-- statement:
--   Let $A,B,C$ be finite-dimensional complex Hilbert spaces, $X\in L(A\otimes B)$ and $D,E:B\to C$ independent linear operators. Then
--   $$ \operatorname{tr}_C[(I_A\otimes D)X(I_A\otimes E^\dagger)]
--   =\operatorname{tr}_B[(I_A\otimes E^\dagger D)X]. $$
--   The rectangular identity allows partial traces to move across isometries between different Weyl registers.
--
--   Differences from the source:
--   - encoding: arbitrary finite-dimensional complex Hilbert spaces A, B, C → matrices on arbitrary finite basis types, including zero-dimensional types; reason: orthonormal coordinates identify every such Hilbert space with one of these instances
-- source:
--   Angus Lowe, Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), Lemma B.1, p.22. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf

import Definitions.Def_RandomDimReduction_Channel_Tensor

set_option autoImplicit false

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ENNReal

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma B.1, p.22: D and E are independent rectangular operators. -/
theorem lemma_B_1 {a b c : Type} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (X : Op (a × b)) (D E : Matrix c b ℂ) :
    WildeQIT.partialTraceRight
      (Matrix.kronecker (1 : Op a) D * X * Matrix.kronecker (1 : Op a) Eᴴ) =
    WildeQIT.partialTraceRight (Matrix.kronecker (1 : Op a) (Eᴴ * D) * X) := by sorry

end RandomDimReduction.Channel
