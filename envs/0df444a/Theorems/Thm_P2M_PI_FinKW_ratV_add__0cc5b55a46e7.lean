-- Prove2me | Theorems.Thm_P2M_PI_FinKW_ratV_add__0cc5b55a46e7
-- name    : P2M_PI_FinKW_ratV_add__0cc5b55a46e7
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:31:34.959019+00:00
-- url     : https://prove2.me/theorems/ded27e60-cf68-4f21-af9b-1f2d4b847951
-- title:
--   P2 M PI Fin KW rat V add  0cc5b55a46e7: P2 M PI Fin KW rat V add  0cc5b55a46e7
-- statement:
--   The P2 M PI Fin KW rat V add  0cc5b55a46e7 construction uses the P2 M PI Fin KW rat V add  0cc5b55a46e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/LocFrom.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/LocFrom.lean#L12-L16

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

theorem P2M_PI_FinKW_ratV_add__0cc5b55a46e7 {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {n : ℕ} (a b : Fin n → E) :
    Formalism.L2.SG.Sub.ratV (F := F) R (a + b) = Formalism.L2.SG.Sub.ratV (F := F) R a + Formalism.L2.SG.Sub.ratV (F := F) R b := by sorry

alias «PI».«FinKW».«ratV_add'» := P2M_PI_FinKW_ratV_add__0cc5b55a46e7
