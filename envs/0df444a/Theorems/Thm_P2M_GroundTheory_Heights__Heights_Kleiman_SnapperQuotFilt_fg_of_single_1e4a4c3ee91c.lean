-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_fg_of_single_1e4a4c3ee91c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_fg_of_single_1e4a4c3ee91c
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:57:46.552044+00:00
-- url     : https://prove2.me/theorems/5048d660-afc1-42d5-a541-05ad791d642f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt fg of single 1e4a4c3ee91c: P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt fg of single 1e4a4c3ee91c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt fg of single 1e4a4c3ee91c construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt fg of single 1e4a4c3ee91c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/HomogeneousComponentMulForm.lean#L150-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/HomogeneousComponentMulForm.lean#L150-L177

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_HomogeneousComponentMulForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotFilt
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
omit [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_fg_of_single_1e4a4c3ee91c (F : SubFamily S x E) (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) (hxi : x i ≠ 0)
    (hfg : (F.sub (singleChart hxi)).FG) : (F.sub I).FG := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperQuotFilt».«fg_of_single» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_fg_of_single_1e4a4c3ee91c
