-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_claim_kill_e71d0cb7bfe0
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_claim_kill_e71d0cb7bfe0
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:02:32.864682+00:00
-- url     : https://prove2.me/theorems/ccffe501-e922-5832-92a9-a37cbe709db8
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman claim kill e71d0cb7bfe0: P2 M Ground Theory Heights  Heights Kleiman claim kill e71d0cb7bfe0
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman claim kill e71d0cb7bfe0 construction uses the P2 M Ground Theory Heights  Heights Kleiman claim kill e71d0cb7bfe0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimVanish.lean#L78-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimVanish.lean#L78-L90

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_claim_kill_e71d0cb7bfe0 : ∀ (f : Poly k N) (e : ℕ), f ∈ T.J → f.IsHomogeneous e → ∀ (a : ℤ),
    ∀ z ∈ (coordGraded k x).piece a, aeval x f • z ∈ Jg.piece (a + e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«claim_kill» := P2M_GroundTheory_Heights__Heights_Kleiman_claim_kill_e71d0cb7bfe0
