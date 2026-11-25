-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_polydisc_differentiable_cons
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.polydisc_differentiable_cons
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:54:12.470821+00:00
-- url     : https://prove2.me/theorems/2ffdc7fc-3240-479d-8100-0394b115be6d
-- title:
--   Geometry Of Numbers Theory: polydisc differentiable cons
-- statement:
--   The Geometry Of Numbers Theory construction uses the polydisc differentiable cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/PolydiscSt.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/PolydiscSt.lean#L15-L22

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_DiscSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_PolydiscSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory

theorem ReciprocityTheory.GeometryOfNumbersTheory.polydisc_differentiable_cons {D : ℕ} :
    Differentiable ℂ (fun p : ℂ × (Fin D → ℂ) => (Fin.cons p.1 p.2 : Fin (D + 1) → ℂ)) := by sorry
