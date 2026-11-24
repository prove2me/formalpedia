-- Prove2me | Theorems.Thm_PI_ScRefExists_TH_mem_cj
-- name    : PI.ScRefExists.TH.mem_cj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:14:35.865811+00:00
-- url     : https://prove2.me/theorems/e63e5ea7-b2f4-4851-9743-a2dad542e187
-- title:
--   TH: mem cj
-- statement:
--   The TH construction uses the mem cj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/ThetaA.lean#L61-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/ThetaA.lean#L61-L62

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.TH
variable (I : Formalism.MainNotions.S.AutInst)

theorem PI.ScRefExists.TH.mem_cj (P : HeightOneSpectrum (𝓞 I.E)) (x : 𝓞 I.E) : x ∈ (cj I P).asIdeal ↔ sg I x ∈ P.asIdeal := by sorry
