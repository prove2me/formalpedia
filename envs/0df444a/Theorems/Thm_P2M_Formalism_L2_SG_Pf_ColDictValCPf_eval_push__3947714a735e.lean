-- Prove2me | Theorems.Thm_P2M_Formalism_L2_SG_Pf_ColDictValCPf_eval_push__3947714a735e
-- name    : P2M_Formalism_L2_SG_Pf_ColDictValCPf_eval_push__3947714a735e
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:31:36.72279+00:00
-- url     : https://prove2.me/theorems/fcaf5cee-970d-408b-8b8c-7e342869ca36
-- title:
--   P2 M Formalism L2 SG Pf Col Dict Val CPf eval push  3947714a735e: P2 M Formalism L2 SG Pf Col Dict Val CPf eval push  3947714a735e
-- statement:
--   The P2 M Formalism L2 SG Pf Col Dict Val CPf eval push  3947714a735e construction uses the P2 M Formalism L2 SG Pf Col Dict Val CPf eval push  3947714a735e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/DivisorClosedHolds.lean#L42-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/DivisorClosedHolds.lean#L42-L51

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivisorClosedHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ColDictValCPf
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.L2.SG.Pf.ColDictPf Matrix MvPolynomial
open scoped ComplexOrder
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem P2M_Formalism_L2_SG_Pf_ColDictValCPf_eval_push__3947714a735e (φ : Module.Dual ℂ (MvPolynomial (ι × Fin n × Fin n) ℂ)) (x : Fin n × Fin n → ℂ)
    (Q : MvPolynomial (ι × Fin n × Fin n) (MvPolynomial (Fin n × Fin n) ℂ)) :
    eval x (pushφ φ Q) = φ (map (eval x) Q) := by sorry

alias «Formalism».«L2».«SG».«Pf».«ColDictValCPf».«eval_pushφ» := P2M_Formalism_L2_SG_Pf_ColDictValCPf_eval_push__3947714a735e
