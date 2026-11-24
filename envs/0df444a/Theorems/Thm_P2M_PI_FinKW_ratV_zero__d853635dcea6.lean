-- Prove2me | Theorems.Thm_P2M_PI_FinKW_ratV_zero__d853635dcea6
-- name    : P2M_PI_FinKW_ratV_zero__d853635dcea6
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:31:32.120317+00:00
-- url     : https://prove2.me/theorems/cae1cb4c-5ec5-4596-8eb2-0e114cfd9019
-- title:
--   P2 M PI Fin KW rat V zero  d853635dcea6: P2 M PI Fin KW rat V zero  d853635dcea6
-- statement:
--   The P2 M PI Fin KW rat V zero  d853635dcea6 construction uses the P2 M PI Fin KW rat V zero  d853635dcea6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/LocFrom.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/LocFrom.lean#L18-L21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocFrom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FinKW
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)

theorem P2M_PI_FinKW_ratV_zero__d853635dcea6 {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {n : ℕ} : Formalism.L2.SG.Sub.ratV (F := F) R (0 : Fin n → E) = 0 := by sorry

alias «PI».«FinKW».«ratV_zero'» := P2M_PI_FinKW_ratV_zero__d853635dcea6
