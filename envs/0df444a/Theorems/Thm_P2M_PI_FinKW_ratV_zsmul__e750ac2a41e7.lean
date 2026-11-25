-- Prove2me | Theorems.Thm_P2M_PI_FinKW_ratV_zsmul__e750ac2a41e7
-- name    : P2M_PI_FinKW_ratV_zsmul__e750ac2a41e7
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:55:57.757428+00:00
-- url     : https://prove2.me/theorems/e02d113d-d1b7-59bf-a68c-868ccabdb1ba
-- title:
--   P2 M PI Fin KW rat V zsmul  e750ac2a41e7: P2 M PI Fin KW rat V zsmul  e750ac2a41e7
-- statement:
--   The P2 M PI Fin KW rat V zsmul  e750ac2a41e7 construction uses the P2 M PI Fin KW rat V zsmul  e750ac2a41e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/LocFrom.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/LocFrom.lean#L23-L27

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

theorem P2M_PI_FinKW_ratV_zsmul__e750ac2a41e7 {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {n : ℕ} (k : ℤ) (a : Fin n → E) :
    Formalism.L2.SG.Sub.ratV (F := F) R (k • a) = k • Formalism.L2.SG.Sub.ratV (F := F) R a := by sorry

alias «PI».«FinKW».«ratV_zsmul'» := P2M_PI_FinKW_ratV_zsmul__e750ac2a41e7
