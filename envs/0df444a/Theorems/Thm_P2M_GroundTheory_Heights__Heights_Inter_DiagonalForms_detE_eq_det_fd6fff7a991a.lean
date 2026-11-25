-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_detE_eq_det_fd6fff7a991a
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_detE_eq_det_fd6fff7a991a
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:23:49.944724+00:00
-- url     : https://prove2.me/theorems/8546afff-081e-42e4-95f5-c36afc66f7f2
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Forms det E eq det fd6fff7a991a: P2 M Ground Theory Heights  Heights Inter Diagonal Forms det E eq det fd6fff7a991a
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Forms det E eq det fd6fff7a991a construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Forms det E eq det fd6fff7a991a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L131-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L131-L134

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalForms
variable {Ω : Type*} [Field Ω] {ι : Type*} {E : Type*} [AddCommGroup E] [Module Ω E] {x : ι → Ω}

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_detE_eq_det_fd6fff7a991a (e b : Module.Basis (Fin 2) Ω E) : T.detE e (b 0) (b 1) = e.det b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalForms».«detE_eq_det» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_detE_eq_det_fd6fff7a991a
