-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_claim_le_346deb24d81f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_claim_le_346deb24d81f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:05:02.886622+00:00
-- url     : https://prove2.me/theorems/56165819-075e-55ff-b42a-ff2401c4107e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman claim le 346deb24d81f: P2 M Ground Theory Heights  Heights Kleiman claim le 346deb24d81f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman claim le 346deb24d81f construction uses the P2 M Ground Theory Heights  Heights Kleiman claim le 346deb24d81f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimVanish.lean#L69-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimVanish.lean#L69-L74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanishCech
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanish
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
variable (T : StepData k x) (Jg : FinGradedSub (S := k) (x := x) Ω)
  (hJg : ∀ c : ℤ, Jg.piece c = Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ T.J ∧
    f.IsHomogeneous e ∧ (e : ℤ) = c ∧ z = aeval x f})
include hJg

theorem P2M_GroundTheory_Heights__Heights_Kleiman_claim_le_346deb24d81f : ∀ c, Jg.piece c ≤ (coordGraded k x).piece c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«claim_le» := P2M_GroundTheory_Heights__Heights_Kleiman_claim_le_346deb24d81f
