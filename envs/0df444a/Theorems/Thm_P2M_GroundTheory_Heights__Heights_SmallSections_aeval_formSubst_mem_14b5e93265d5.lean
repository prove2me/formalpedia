-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_aeval_formSubst_mem_14b5e93265d5
-- name    : P2M_GroundTheory_Heights__Heights_SmallSections_aeval_formSubst_mem_14b5e93265d5
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:38:10.072356+00:00
-- url     : https://prove2.me/theorems/700bf8b7-9df6-46fa-a861-fdb28ccd0757
-- title:
--   P2 M Ground Theory Heights  Heights Small Sections aeval form Subst mem 14b5e93265d5: P2 M Ground Theory Heights  Heights Small Sections aeval form Subst mem 14b5e93265d5
-- statement:
--   The P2 M Ground Theory Heights  Heights Small Sections aeval form Subst mem 14b5e93265d5 construction uses the P2 M Ground Theory Heights  Heights Small Sections aeval form Subst mem 14b5e93265d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L174-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L174-L192

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousAeval
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SmallSections
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_SmallSections_aeval_formSubst_mem_14b5e93265d5 {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ} (hg : D.IsFormSystem d g)
    {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) {f : MvPolynomial (Coord D.extSizes) ℤ}
    (hf : f ∈ D.extIdeal) : aeval (formSubst D g c) f ∈ P.ideal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SmallSections».«aeval_formSubst_mem» := P2M_GroundTheory_Heights__Heights_SmallSections_aeval_formSubst_mem_14b5e93265d5
