-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_isSS_coeff
-- name    : PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac.isSS_coeff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:48:05.545016+00:00
-- url     : https://prove2.me/theorems/ba6eba46-2595-4180-9045-f5531bc305ec
-- title:
--   Sep Fac: is SS coeff
-- statement:
--   The Sep Fac construction uses the is SS coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PSepFacB.lean#L62-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PSepFacB.lean#L62-L150

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFac
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFacB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.Cz PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
variable {B : Type} [CommRing B] [Algebra ℂ B]

theorem PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac.isSS_coeff (p : ℂ[X]) (hp : p.Separable) (P Q : B[X]) (hP : P.Monic) (hQ : Q.Monic)
    (hPQ : P * Q = p.map (algebraMap ℂ B)) (k : ℕ) : IsSS (P.coeff k) := by sorry
