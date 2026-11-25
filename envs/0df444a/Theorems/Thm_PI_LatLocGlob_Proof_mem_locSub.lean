-- Prove2me | Theorems.Thm_PI_LatLocGlob_Proof_mem_locSub
-- name    : PI.LatLocGlob.Proof.mem_locSub
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:34:09.092544+00:00
-- url     : https://prove2.me/theorems/156f1178-e54f-49d4-801d-502510264884
-- title:
--   Proof: mem loc Sub
-- statement:
--   The Proof construction uses the mem loc Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalGlobalLattice/ExistsSmulMemOfLocal.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalGlobalLattice/ExistsSmulMemOfLocal.lean#L34-L35

import Definitions.Def_Formalism_PeriodIntegrals_LatLocGlob
import Definitions.Def_Lemmata_GeneralBFactThirdBisAlt_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalLattice_ExistsSmulMemOfLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LatLocGlob PI.LatLocGlob.Proof
open PI.LatLocGlob
variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]

theorem PI.LatLocGlob.Proof.mem_locSub {p : Ideal R} {hp : p.IsPrime} {N : Submodule R V} {x : V} :
    x ∈ locSub p hp N ↔ x ∈ loc p N := by sorry
