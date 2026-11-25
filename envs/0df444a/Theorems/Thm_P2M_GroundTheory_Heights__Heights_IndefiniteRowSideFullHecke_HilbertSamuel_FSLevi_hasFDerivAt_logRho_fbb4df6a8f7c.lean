-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_hasFDerivAt_logRho_fbb4df6a8f7c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_hasFDerivAt_logRho_fbb4df6a8f7c
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:17.972236+00:00
-- url     : https://prove2.me/theorems/1099cf4d-5d33-5ec0-b11c-62012506680d
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samuel FSLevi has FDeriv At log Rho fbb4df6a8f7c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samuel FSLevi has FDeriv At log Rho fbb4df6a8f7c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samuel FSLevi has FDeriv At log Rho fbb4df6a8f7c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/FderivFderivLogRho.lean#L63-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/FderivFderivLogRho.lean#L63-L72

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_hasFDerivAt_logRho_fbb4df6a8f7c {z : J → ℂ} (hz : z ≠ 0) :
    HasFDerivAt (fun z ↦ Real.log ((fsMetric J).ρ z)) ((nsq z)⁻¹ • bil z) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«HilbertSamuel».«FSLevi».«hasFDerivAt_logRho» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_hasFDerivAt_logRho_fbb4df6a8f7c
