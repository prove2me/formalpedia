-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P88_trace_gram_dual_equivalences
-- name    : QAlgorithms.Papers.Independent.Intake100.P88.trace_gram_dual_equivalences
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:41:30.032319+00:00
-- url     : https://prove2.me/theorems/5f959d96-d878-4947-b3eb-c1c1b120a543
-- title:
--   Lemma 5.1: trace form, Gram determinant and dual basis
-- statement:
--   Let $A$ be a finite-dimensional unital algebra over a field $F$, let $t:A\to F$ be linear with $t(ab)=t(ba)$, and let $(b_i)_{i\in I}$ be a finite basis. Set $G_{ij}=t(b_i b_j)$. The following are equivalent:
--
--   $$\bigl(\forall b\ne0\ \exists a,\ t(ba)\ne0\bigr)
--   \quad\Longleftrightarrow\quad\det G\ne0
--   \quad\Longleftrightarrow\quad
--   \exists\text{ a basis }(b_i^*),\ t(b_i b_j^*)=\delta_{ij}.$$
--
--   The nonzero qualification follows the source's proof, correcting its preceding prose. This criterion supplies actual dual bases for trace averaging, including the zero-dimensional algebra with empty Gram determinant one.
-- source:
--   Partition Algebras, arXiv:math/0401314v2, PDF p. 39, Lemma 5.1: trace form, Gram determinant and dual basis

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P88

attribute [local instance] Classical.propDecidable

open scoped BigOperators Matrix

open QAlgorithms.Papers.Independent.Information100.P65 (hookLength)

open QAlgorithms.Papers.Independent.Renew46.P30 (TensorIndex)

universe u v w x y

/-- Nondegeneracy, determinant, and existence of dual basis, PDF p.39, Lemma 5.1.
SOURCE CORRECTION: nondegeneracy tests nonzero `b`, as the proof explicitly requires. -/
theorem trace_gram_dual_equivalences (F A I : Type*) [Field F] [Ring A] [Algebra F A]
    [FiniteDimensional F A] [Fintype I] [DecidableEq I]
    (t : A →ₗ[F] F) (_htrace : ∀ a b : A, t (a * b) = t (b * a)) (b : Module.Basis I F A) :
    (TraceNondegenerate (fun a => t a) ↔ (traceGram t b).det ≠ 0) ∧
    ((traceGram t b).det ≠ 0 ↔ ∃ c : Module.Basis I F A, IsTraceDualBasis t b c) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P88

end
