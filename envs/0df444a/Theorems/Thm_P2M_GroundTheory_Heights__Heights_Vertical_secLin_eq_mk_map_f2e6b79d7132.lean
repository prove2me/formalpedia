-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_secLin_eq_mk_map_f2e6b79d7132
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_secLin_eq_mk_map_f2e6b79d7132
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:43:53.032125+00:00
-- url     : https://prove2.me/theorems/3b08d2a3-a26b-4b13-bed9-1ecf514fa100
-- title:
--   P2 M Ground Theory Heights  Heights Vertical sec Lin eq mk map f2e6b79d7132: P2 M Ground Theory Heights  Heights Vertical sec Lin eq mk map f2e6b79d7132
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical sec Lin eq mk map f2e6b79d7132 construction uses the P2 M Ground Theory Heights  Heights Vertical sec Lin eq mk map f2e6b79d7132 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecLength.lean#L57-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecLength.lean#L57-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Vertical_secLin_eq_mk_map_f2e6b79d7132 {K : Type*} [Field K] [NumberField K] {n e : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) (u : Fin n → 𝓞 K) :
    secLin (modelR e I v) (parY e n v) (fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j)) =
      Ideal.Quotient.mk _ ((linForm u).map (algebraMap (𝓞 K) (ParDVR e n v))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«secLin_eq_mk_map» := P2M_GroundTheory_Heights__Heights_Vertical_secLin_eq_mk_map_f2e6b79d7132
