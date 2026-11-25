-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_mkF_aeval_forms_d6606fc0914c
-- name    : P2M_GroundTheory_Heights__Heights_SmallSections_mkF_aeval_forms_d6606fc0914c
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:38:06.545574+00:00
-- url     : https://prove2.me/theorems/d8fe8327-c018-4758-b6bf-6d9645400be2
-- title:
--   P2 M Ground Theory Heights  Heights Small Sections mk F aeval forms d6606fc0914c: P2 M Ground Theory Heights  Heights Small Sections mk F aeval forms d6606fc0914c
-- statement:
--   The P2 M Ground Theory Heights  Heights Small Sections mk F aeval forms d6606fc0914c construction uses the P2 M Ground Theory Heights  Heights Small Sections mk F aeval forms d6606fc0914c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L74-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L74-L80

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

theorem P2M_GroundTheory_Heights__Heights_SmallSections_mkF_aeval_forms_d6606fc0914c {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ} (hg : D.IsFormSystem d g)
    {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) {τ : ℕ} {F : MvPolynomial (Fin (D.size + 1)) ℤ}
    (hF : F.IsHomogeneous τ) :
    P.mkF (aeval (g c) F) = P.mkF (chartMonomial c d) ^ τ * aeval D.elt F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SmallSections».«mkF_aeval_forms» := P2M_GroundTheory_Heights__Heights_SmallSections_mkF_aeval_forms_d6606fc0914c
