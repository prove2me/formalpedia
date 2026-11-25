-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace__bb7ee37dbac7
-- name    : P2M_GlobalTheory_T_finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace__bb7ee37dbac7
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:10:06.632147+00:00
-- url     : https://prove2.me/theorems/66c448db-68a3-429e-b232-3f7621d999ec
-- title:
--   P2 M Global Theory T finrank ker aeval eq nat Degree mul finrank eigenspace  bb7ee37dbac7: P2 M Global Theory T finrank ker aeval eq nat Degree mul finrank eigenspace  bb7ee37dbac7
-- statement:
--   The P2 M Global Theory T finrank ker aeval eq nat Degree mul finrank eigenspace  bb7ee37dbac7 construction uses the P2 M Global Theory T finrank ker aeval eq nat Degree mul finrank eigenspace  bb7ee37dbac7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAlStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAlStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAlStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace__bb7ee37dbac7 : ∀ (F : Type) [Field F] [Finite F] (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι F) (f : F[X]) (y : AlgebraicClosure F), Irreducible f → aeval y f = 0 → Module.finrank F (LinearMap.ker (aeval (Matrix.toLin' M) f)) = f.natDegree * Module.finrank (AlgebraicClosure F) (Module.End.eigenspace (Matrix.toLin' (M.map (algebraMap F (AlgebraicClosure F)))) y) := by sorry

alias «GlobalTheory».«T».«finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace'» := P2M_GlobalTheory_T_finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace__bb7ee37dbac7
