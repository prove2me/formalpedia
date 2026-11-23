-- Prove2me | Theorems.Thm_PI_LocFramePrimWork_Assemble_smul_eq
-- name    : PI.LocFramePrimWork.Assemble_smul_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:27.804887+00:00
-- url     : https://prove2.me/theorems/feb20ff6-b648-4a0e-a06b-8997d3ec1730
-- title:
--   Loc Frame Prim Work: Assemble smul eq
-- statement:
--   The Loc Frame Prim Work construction uses the Assemble smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/Assemble.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/Assemble.lean#L26-L31

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_Assemble
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

theorem PI.LocFramePrimWork.Assemble_smul_eq (t : v.adicCompletionIntegers F) (x : Fin n → Fv F v ⊗[F] E) :
    t • x = sc (E := E) v (t : Fv F v) • x := by sorry
