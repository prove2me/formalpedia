-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_fg_of_le_cd87d9f58845
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_fg_of_le_cd87d9f58845
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:27:52.924975+00:00
-- url     : https://prove2.me/theorems/06e3315f-5e6f-4633-93c0-02c2ce565fcc
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt fg of le cd87d9f58845: P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt fg of le cd87d9f58845
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt fg of le cd87d9f58845 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt fg of le cd87d9f58845 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/HomogeneousComponentMulForm.lean#L181-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/HomogeneousComponentMulForm.lean#L181-L188

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_fg_of_le_cd87d9f58845 [IsNoetherianRing S] (F G : SubFamily S x E) (hF : ∀ I, (F.sub I).FG)
    (hle : ∀ I, G.sub I ≤ F.sub I) (I : Chart x) : (G.sub I).FG := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperQuotFilt».«fg_of_le» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_fg_of_le_cd87d9f58845
