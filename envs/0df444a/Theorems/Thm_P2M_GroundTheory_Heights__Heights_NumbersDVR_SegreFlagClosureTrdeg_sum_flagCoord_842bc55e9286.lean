-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagClosureTrdeg_sum_flagCoord_842bc55e9286
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagClosureTrdeg_sum_flagCoord_842bc55e9286
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:09:00.767386+00:00
-- url     : https://prove2.me/theorems/e7fdbf90-6c9a-47a1-a117-6b7a85c4eff8
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Closure Trdeg sum flag Coord 842bc55e9286: P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Closure Trdeg sum flag Coord 842bc55e92
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Closure Trdeg sum flag Coord 842bc55e9286 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Closure Trdeg sum flag Coord 842bc55e9286 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagClosureTrdeg.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagClosureTrdeg.lean#L15-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagConeAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PAdjoinTrdegAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairConeLinesIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosureTrdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureTrdeg

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagClosureTrdeg_sum_flagCoord_842bc55e9286 {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ]
    [Algebra Ω Φ] {N k : ℕ} (hkN : k ≤ N) (w e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ) (a : Fin N → Φ) :
    ∑ j, flagCoord w e t k j * a j =
      ∑ j : Fin k, flagCoord w e t k (Fin.castLE hkN j) * a (Fin.castLE hkN j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«SegreFlagClosureTrdeg».«sum_flagCoord» := P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagClosureTrdeg_sum_flagCoord_842bc55e9286
