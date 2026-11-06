-- Prove2me | Theorems.Thm_RecursionWithPieces_tiedAllCal
-- name    : RecursionWithPieces.tiedAllCal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:07:38.622003+00:00
-- url     : https://prove2.me/theorems/a72bfdc6-7516-4fdb-9b5e-2be2f7d9df69
-- title:
--   Recursion With Pieces: tied All Cal
-- statement:
--   **The end theorem, tied to its function.** There are a constant c and programs (P₀, val) for the
--   pieces of Appendix B such that: the recursion of Appendix A on them, on the schedule of display (40)
--   with the least x₀ of the theorem on the
--   general recursion, satisfies parts (b) and (c), first sentence, of that theorem; the function
--   `fnAll StepSparsify.thCal`, which sparsifies with the thresholds `StepSparsify.thCal`
--   (proof/variables/RecursionWithPieces/Defs.lean says what they are), counts each output by Steps 1 to
--   4 of Appendix D (`VariableBound.countD`) on that recursion,
--   with the level chosen by the named program `pickAB`, and is merged with the algorithm for the bound
--   in m on the same recursion, is with the exponent function `expAll` an algorithm for the rates of
--   Theorem 1; one machine puts out its value
--   on every input, with the pad of 2^(expAll x) units, and counts within the three bounds; a second
--   machine does the same for «some bit is 1»; and for every width and all large n the plan is used. The
--   statement fixes what the machines put out
--   and a bound on their steps, not the steps themselves; it names the algorithm and does not force the
--   argument by which the groupings exist, nor the way in which a network at the top level is handed to
--   the solver. The constant c and the programs are existentially quantified. What differs from the
--   printed text is listed in
--   proof/variables/RecursionWithPieces/Defs.lean.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionWithPieces/Main.lean#L190-L190
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionWithPieces/Main.lean#L190-L190

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInKStatement
import Definitions.Def_RecursionWithPieces_Defs
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_RecursionWithPieces_Master
import Definitions.Def_GeneralPieces_Main
import Definitions.Def_GeneralPieces_Tied_Bound
import Definitions.Def_GeneralPieces_Top_CaseI
import Definitions.Def_GeneralPieces_Num_TopDisplay
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_ClauseBound_Alg_Need
import Definitions.Def_SparsifyThenCount_Main
import Definitions.Def_SparsifyThenCount_PlanUsed
import Definitions.Def_SparsifyThenCount_Correct
import Definitions.Def_SparsifyThenCount_CorrectB
import Definitions.Def_SparsifyThenCount_Tied
import Definitions.Def_VariableBound_MainPrinted
import Definitions.Def_VariableBound_Printed_Tied
import Definitions.Def_VariableBound_Paper_Decide
import Definitions.Def_VariableBound_StepParity
import Definitions.Def_VariableBound_Family_Main
import Definitions.Def_VariableBound_Field_Family
import Definitions.Def_VariableBound_Params_Spec
import Definitions.Def_VariableBound_Params_Ineq
import Definitions.Def_VariableBound_Search_Correct
import Definitions.Def_VariableBound_Net_Main
import Definitions.Def_VariableBound_Net_Ev
import Definitions.Def_VariableBound_Count_Correct
import Definitions.Def_VariableBound_Top_Budget
import Definitions.Def_VariableBound_Top_ArithPlan
import Definitions.Def_StepSparsify_WalkCount
import Definitions.Def_StepSparsify_CalServes
import Definitions.Def_UniformInK_Top_Correct
import Definitions.Def_UniformInK_Top_CorrectB
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_ClauseBound_MainBoth
import Definitions.Def_ClauseBound_Both_TimeM
import Definitions.Def_ClauseBound_Alg_TopVal
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_RecursionWithPieces_Main
set_option autoImplicit false
section
section
open RecursionWithPieces
open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Both ClauseBound.ParityChecks ClauseBound.TopN UniformInK VariableBound VariableBound.Decide SparsifyThenCount GeneralPieces

theorem RecursionWithPieces.tiedAllCal : TiedAllCal := by sorry
