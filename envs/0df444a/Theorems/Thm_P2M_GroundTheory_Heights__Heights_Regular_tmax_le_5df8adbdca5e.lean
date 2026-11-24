-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_tmax_le_5df8adbdca5e
-- name    : P2M_GroundTheory_Heights__Heights_Regular_tmax_le_5df8adbdca5e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:48.58658+00:00
-- url     : https://prove2.me/theorems/b8d296af-2672-4de3-9d2d-4652dc096d5e
-- title:
--   P2 M Ground Theory Heights  Heights Regular tmax le 5df8adbdca5e: P2 M Ground Theory Heights  Heights Regular tmax le 5df8adbdca5e
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular tmax le 5df8adbdca5e construction uses the P2 M Ground Theory Heights  Heights Regular tmax le 5df8adbdca5e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/RegMaxReindex.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/RegMaxReindex.lean#L25-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_RegMaxReindex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory
open ReciprocityTheory.AnForm.A (regMax tmax kθ)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_tmax_le_5df8adbdca5e {ι : Type*} [Fintype ι] [Nonempty ι] {t : ι → ℝ} {c : ℝ} (h : ∀ i, t i ≤ c) :
    tmax t ≤ c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«tmax_le» := P2M_GroundTheory_Heights__Heights_Regular_tmax_le_5df8adbdca5e
