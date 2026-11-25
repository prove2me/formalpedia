-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_cs_011f677b3d11
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_cs_011f677b3d11
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:10.660461+00:00
-- url     : https://prove2.me/theorems/90d95c2f-6f85-5120-8688-6c9601ea4e9a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samuel FSLevi cs 011f677b3d11: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samuel FSLevi cs 01
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samuel FSLevi cs 011f677b3d11 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samuel FSLevi cs 011f677b3d11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/FderivFderivLogRho.lean#L92-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/FderivFderivLogRho.lean#L92-L117

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IsConeAnalyticSubset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_FderivFderivLogRho
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.FSLevi
variable {J : Type} [Fintype J]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_cs_011f677b3d11 (z w : J → ℂ) :
    (∑ p, (reP p z * reP p w + imaginary p z * imaginary p w)) ^ 2 +
      (∑ p, (reP p z * reP p (Complex.I • w) + imaginary p z * imaginary p (Complex.I • w))) ^ 2 ≤
      nsq z * nsq w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«HilbertSamuel».«FSLevi».«cs» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_cs_011f677b3d11
