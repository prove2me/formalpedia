-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_idealChart_prod_le_4c75a5f4b0ed
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_idealChart_prod_le_4c75a5f4b0ed
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:11:59.062634+00:00
-- url     : https://prove2.me/theorems/94225e31-e61f-5074-9b21-4ccef552c7e1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman ideal Chart prod le 4c75a5f4b0ed: P2 M Ground Theory Heights  Heights Kleiman ideal Chart prod le 4c75a5f4b0ed
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman ideal Chart prod le 4c75a5f4b0ed construction uses the P2 M Ground Theory Heights  Heights Kleiman ideal Chart prod le 4c75a5f4b0ed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThree.lean#L53-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThree.lean#L53-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnW
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThree
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
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_idealChart_prod_le_4c75a5f4b0ed {ι : Type*} (s : Finset ι) (P : ι → Ideal (Poly k N)) (I : Chart x) :
    ∏ i ∈ s, idealChart (P i) I ≤ idealChart (x := x) (∏ i ∈ s, P i) I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«idealChart_prod_le» := P2M_GroundTheory_Heights__Heights_Kleiman_idealChart_prod_le_4c75a5f4b0ed
