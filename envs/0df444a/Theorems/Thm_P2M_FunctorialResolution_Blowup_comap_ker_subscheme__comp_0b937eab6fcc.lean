-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_Blowup_comap_ker_subscheme__comp_0b937eab6fcc
-- name    : P2M_FunctorialResolution_Blowup_comap_ker_subscheme__comp_0b937eab6fcc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:40.265854+00:00
-- url     : https://prove2.me/theorems/b69664fa-1ed0-496f-be94-abf94ed086fb
-- title:
--   P2 M Functorial Resolution Blowup comap ker subscheme  comp 0b937eab6fcc: P2 M Functorial Resolution Blowup comap ker subscheme  comp 0b937eab6fcc
-- statement:
--   The P2 M Functorial Resolution Blowup comap ker subscheme  comp 0b937eab6fcc construction uses the P2 M Functorial Resolution Blowup comap ker subscheme  comp 0b937eab6fcc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/StrictTransform.lean#L62-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/StrictTransform.lean#L62-L77

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open FunctorialResolution FunctorialResolution.Blowup
noncomputable section

theorem P2M_FunctorialResolution_Blowup_comap_ker_subscheme__comp_0b937eab6fcc {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] (I : X.IdealSheafData) :
    ((I.subschemeι ≫ f).ker).comap f = I := by sorry

alias «FunctorialResolution».«Blowup».«comap_ker_subschemeι_comp» := P2M_FunctorialResolution_Blowup_comap_ker_subscheme__comp_0b937eab6fcc
