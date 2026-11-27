-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_twistPows_eq_1c2add2714bc
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_twistPows_eq_1c2add2714bc
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:30:44.512101+00:00
-- url     : https://prove2.me/theorems/ac5a99a5-26c3-5abd-9673-8a4a4f064f20
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt twist Pows eq 1c2add2714bc: P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt twist Pows eq 1c2add2714bc
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt twist Pows eq 1c2add2714bc construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt twist Pows eq 1c2add2714bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/HomogeneousComponentMulForm.lean#L59-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/HomogeneousComponentMulForm.lean#L59-L68

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_twistPows_eq_1c2add2714bc (F : SubSystem S x E) : ∀ (t : ℕ) (L : Fin t → LineBundle S x) (n : Fin t → ℕ),
    F.twistPows t (fun j => (L j).toSubSystem) n = F.twist (powsBundle t L n).toSubSystem
  := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperQuotFilt».«twistPows_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_twistPows_eq_1c2add2714bc
