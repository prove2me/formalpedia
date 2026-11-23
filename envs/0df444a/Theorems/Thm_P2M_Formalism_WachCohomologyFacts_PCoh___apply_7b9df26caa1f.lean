-- Prove2me | Theorems.Thm_P2M_Formalism_WachCohomologyFacts_PCoh___apply_7b9df26caa1f
-- name    : P2M_Formalism_WachCohomologyFacts_PCoh___apply_7b9df26caa1f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:43.464801+00:00
-- url     : https://prove2.me/theorems/07e47ffc-2e97-41d8-8f94-12a457061f8a
-- title:
--   P2 M Formalism Wach Cohomology Facts PCoh   apply 7b9df26caa1f: P2 M Formalism Wach Cohomology Facts PCoh   apply 7b9df26caa1f
-- statement:
--   The P2 M Formalism Wach Cohomology Facts PCoh   apply 7b9df26caa1f construction uses the P2 M Formalism Wach Cohomology Facts PCoh   apply 7b9df26caa1f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusContraction/FrobeniusContractionProofs/FiniteCocyclesLeCocycles.lean#L16-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusContraction/FrobeniusContractionProofs/FiniteCocyclesLeCocycles.lean#L16-L16

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

theorem P2M_Formalism_WachCohomologyFacts_PCoh___apply_7b9df26caa1f (x : ZMod n → V) (j : ZMod n) : W.Φ x j = W.φ (j - 1) (x (j - 1)) := by sorry

alias «Formalism».«WachCohomologyFacts».«PCoh».«Φ_apply» := P2M_Formalism_WachCohomologyFacts_PCoh___apply_7b9df26caa1f
