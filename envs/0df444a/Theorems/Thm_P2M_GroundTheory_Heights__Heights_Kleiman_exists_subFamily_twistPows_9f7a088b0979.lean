-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_subFamily_twistPows_9f7a088b0979
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_subFamily_twistPows_9f7a088b0979
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:12:13.851466+00:00
-- url     : https://prove2.me/theorems/2e354dd8-836d-592e-92e1-51040ebc49a3
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists sub Family twist Pows 9f7a088b0979: P2 M Ground Theory Heights  Heights Kleiman exists sub Family twist Pows 9f7a088b0979
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists sub Family twist Pows 9f7a088b0979 construction uses the P2 M Ground Theory Heights  Heights Kleiman exists sub Family twist Pows 9f7a088b0979 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotDevissage.lean#L35-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotDevissage.lean#L35-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SubFamilyTwistSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperQuotDevissage
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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_subFamily_twistPows_9f7a088b0979 (hB : SubFamilyTwist.Statement.{u, v, w}) (F : SubFamily S x E)
    (hF : ∀ I, (F.sub I).FG) : ∀ (t : ℕ) (L : Fin t → LineBundle S x) (n : Fin t → ℕ),
      ∃ H : SubFamily S x E, H.toSubSystem = F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n ∧
        ∀ I, (H.sub I).FG
  := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_subFamily_twistPows» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_subFamily_twistPows_9f7a088b0979
