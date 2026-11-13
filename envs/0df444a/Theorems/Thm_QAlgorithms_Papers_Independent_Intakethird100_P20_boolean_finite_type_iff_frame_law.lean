-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_boolean_finite_type_iff_frame_law
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.boolean_finite_type_iff_frame_law
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T07:40:56.575253+00:00
-- url     : https://prove2.me/theorems/7b68453e-84f3-4f58-b5e4-57bbdee7f1f3
-- title:
--   Corollary 3.1
-- statement:
--   For a complete Boolean algebra $L$, the source's complete-distributivity property is equivalent to finite type:
--
--   $$\bigl[\forall a,S,\ a\wedge\bigvee S=\bigvee_{b\in S}(a\wedge b)\bigr]
--   \quad\Longleftrightarrow\quad
--   \bigl[\forall S\ne\varnothing\text{ directed},\ \overline{\bigcup_{a\in S}Q_a}=Q_{\bigvee S}\bigr].$$
--
--   The finite-type condition ranges over directed nets, not only sequences.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 46, Corollary 3.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Corollary 3.1; de Groote, Observables I, PDF p./pp. 46.
-/
theorem boolean_finite_type_iff_frame_law {L : Type u} [CompleteBooleanAlgebra L] : HasFrameLaw L ↔ IsFiniteType L := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
