-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_Blowup_affineBlowupChart_eq_away__6f5d034cade6
-- name    : P2M_FunctorialResolution_Blowup_affineBlowupChart_eq_away__6f5d034cade6
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:02.975574+00:00
-- url     : https://prove2.me/theorems/b2590182-cdd2-4eab-b4d3-89a1204b49d7
-- title:
--   P2 M Functorial Resolution Blowup affine Blowup Chart eq away  6f5d034cade6: P2 M Functorial Resolution Blowup affine Blowup Chart eq away  6f5d034cade6
-- statement:
--   The P2 M Functorial Resolution Blowup affine Blowup Chart eq away  6f5d034cade6 construction uses the P2 M Functorial Resolution Blowup affine Blowup Chart eq away  6f5d034cade6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowup.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowup.lean#L52-L55

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Theorems.Thm_FunctorialResolution_Blowup_reesGenerator_mem_reesGrading

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.Blowup
universe u
variable {R : Type u} [CommRing R]

theorem P2M_FunctorialResolution_Blowup_affineBlowupChart_eq_away__6f5d034cade6 (I : Ideal R) (a : ↥I) :
    affineBlowupChart I a =
      AlgebraicGeometry.Proj.awayι (reesGrading I) (reesGenerator I a) (reesGenerator_mem_reesGrading I a)
        Nat.one_pos := by sorry

alias «FunctorialResolution».«Blowup».«affineBlowupChart_eq_awayι» := P2M_FunctorialResolution_Blowup_affineBlowupChart_eq_away__6f5d034cade6
