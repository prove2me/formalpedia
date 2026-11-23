-- Prove2me | Theorems.Thm_P2M_PI_LocFramePrimWork_Assemble_smul_eq__803d2b5b4bfc
-- name    : P2M_PI_LocFramePrimWork_Assemble_smul_eq__803d2b5b4bfc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:05.797094+00:00
-- url     : https://prove2.me/theorems/d637e950-0c2a-44bf-a482-a2d71ed070f0
-- title:
--   P2 M PI Loc Frame Prim Work Assemble smul eq  803d2b5b4bfc: P2 M PI Loc Frame Prim Work Assemble smul eq  803d2b5b4bfc
-- statement:
--   The P2 M PI Loc Frame Prim Work Assemble smul eq  803d2b5b4bfc construction uses the P2 M PI Loc Frame Prim Work Assemble smul eq  803d2b5b4bfc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/Assemble.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/Assemble.lean#L33-L37

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

theorem P2M_PI_LocFramePrimWork_Assemble_smul_eq__803d2b5b4bfc (t : v.adicCompletionIntegers F) (y : Fv F v ⊗[F] E) :
    t • y = sc (E := E) v (t : Fv F v) * y := by sorry

alias «PI».«LocFramePrimWork».«Assemble_smul_eq'» := P2M_PI_LocFramePrimWork_Assemble_smul_eq__803d2b5b4bfc
