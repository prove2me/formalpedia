-- Prove2me | Theorems.Thm_P2M_Formalism_WachCohomologyFacts_PCoh____comm_26f0b5ea9b7b
-- name    : P2M_Formalism_WachCohomologyFacts_PCoh____comm_26f0b5ea9b7b
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:27.760309+00:00
-- url     : https://prove2.me/theorems/535210ef-20e9-4d95-8b25-0b467329bad2
-- title:
--   P2 M Formalism Wach Cohomology Facts PCoh    comm 26f0b5ea9b7b: P2 M Formalism Wach Cohomology Facts PCoh    comm 26f0b5ea9b7b
-- statement:
--   The P2 M Formalism Wach Cohomology Facts PCoh    comm 26f0b5ea9b7b construction uses the P2 M Formalism Wach Cohomology Facts PCoh    comm 26f0b5ea9b7b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusContraction/FrobeniusContractionProofs/FiniteCocyclesLeCocycles.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusContraction/FrobeniusContractionProofs/FiniteCocyclesLeCocycles.lean#L20-L22

import Definitions.Def_Formalism_FrobeniusContraction_Statement
import Definitions.Def_Formalism_FrobeniusContraction_FrobeniusContractionProofs_FiniteCocyclesLeCocycles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WachCohomologyFacts Formalism.WachCohomologyFacts.PCoh
open Formalism.WachCohomologyFacts
variable {O A AA : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
  [Algebra A AA] [IsScalarTower O A AA] {B : Base O A} {E : Amb B AA} {n : ℕ}
  {V : Type} [AddCommGroup V] [Module AA V] [Module A V] [IsScalarTower A AA V] [Module O V]
  [IsScalarTower O AA V] (W : WachDatum E n V)

theorem P2M_Formalism_WachCohomologyFacts_PCoh____comm_26f0b5ea9b7b (x : ZMod n → V) : W.Γ (W.Φ x) = W.Φ (W.Γ x) := by sorry

alias «Formalism».«WachCohomologyFacts».«PCoh».«ΓΦ_comm» := P2M_Formalism_WachCohomologyFacts_PCoh____comm_26f0b5ea9b7b
