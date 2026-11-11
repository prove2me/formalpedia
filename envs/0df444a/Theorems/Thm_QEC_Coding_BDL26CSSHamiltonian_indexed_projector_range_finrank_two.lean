-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_indexed_projector_range_finrank_two
-- name    : QEC.Coding.BDL26CSSHamiltonian.indexed_projector_range_finrank_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T14:31:46.671599+00:00
-- url     : https://prove2.me/theorems/55e1a155-8462-4fc2-9583-f3a55ed7deeb
-- title:
--   BDL26 CSSHamiltonian: indexed projector range finrank two
-- statement:
--   The BDL26 CSSHamiltonian construction uses the indexed projector range finrank two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDimension.lean#L191-L193
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDimension.lean#L191-L193

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open PauliSymplectic Semantics MultiscaleDecoder
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_e0d1cb1e0b_118
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_e0d1cb1e0b_119

theorem QEC.Coding.BDL26CSSHamiltonian.indexed_projector_range_finrank_two (depth : Nat) (i : LevelIndex depth) :
    Module.finrank ℂ (LinearMap.range (projector S i.val 0)) = 2 := by sorry
