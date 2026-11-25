-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_secs_sup_smul_le_secs_fibre_971306d43c47
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_secs_sup_smul_le_secs_fibre_971306d43c47
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:02:59.109557+00:00
-- url     : https://prove2.me/theorems/46099a62-65b2-4efe-97eb-90ab98836e85
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman secs sup smul le secs fibre 971306d43c47: P2 M Ground Theory Heights  Heights Kleiman secs sup smul le secs fibre 971306d43c47
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman secs sup smul le secs fibre 971306d43c47 construction uses the P2 M Ground Theory Heights  Heights Kleiman secs sup smul le secs fibre 971306d43c47 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFibreRestrKer.lean#L148-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFibreRestrKer.lean#L148-L162

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreRestrKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreSectionsFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrQuotTorsionFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreRestrKer
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
open MvPolynomial Filter
open scoped Pointwise nonZeroDivisors
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_secs_sup_smul_le_secs_fibre_971306d43c47 (Q : SubSystem S x Ω) (qq : Ideal (Poly S N)) (𝔪 : Ideal S) :
    (Q.twist (idealSys x qq)).secs ⊔ 𝔪 • Q.secs ≤
      (Q.twist (idealSys x (qq ⊔ 𝔪.map (C : S →+* Poly S N)))).secs := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«secs_sup_smul_le_secs_fibre» := P2M_GroundTheory_Heights__Heights_Kleiman_secs_sup_smul_le_secs_fibre_971306d43c47
