-- Prove2me | Theorems.Thm_P2M_GlobalTheory_smooth_smoothLocus___comp_f25dce1b6b4e
-- name    : P2M_GlobalTheory_smooth_smoothLocus___comp_f25dce1b6b4e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:13:15.480428+00:00
-- url     : https://prove2.me/theorems/12dc5d98-22e9-4ca6-b05b-20ecc1e21c29
-- title:
--   P2 M Global Theory smooth smooth Locus   comp f25dce1b6b4e: P2 M Global Theory smooth smooth Locus   comp f25dce1b6b4e
-- statement:
--   The P2 M Global Theory smooth smooth Locus   comp f25dce1b6b4e construction uses the P2 M Global Theory smooth smooth Locus   comp f25dce1b6b4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SmoothDense.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SmoothDense.lean#L10-L13

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SmoothDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem P2M_GlobalTheory_smooth_smoothLocus___comp_f25dce1b6b4e {X Y : Scheme.{0}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] : Smooth (f.smoothLocus.ι ≫ f) := by sorry

alias «GlobalTheory».«smooth_smoothLocus_ι_comp» := P2M_GlobalTheory_smooth_smoothLocus___comp_f25dce1b6b4e
