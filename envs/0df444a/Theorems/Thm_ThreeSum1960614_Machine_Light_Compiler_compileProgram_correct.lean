-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_Light_Compiler_compileProgram_correct
-- name    : ThreeSum1960614.Machine.Light.Compiler.compileProgram_correct
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:12:24.006511+00:00
-- url     : https://prove2.me/theorems/d4ea0a43-7179-4516-9ffa-e982e105932a
-- title:
--   Correctness of the complete Light-to-word-RAM compiler
-- statement:
--   Let a Light execution of the designated main procedure, from argument frame $[0,i,j]$ and memory $\mu$, terminate in state $\sigma\prime$ with cost $c$. Assume the compiler's explicit $W$-bit fit inequalities for the execution limits, dispatcher, and stack, and assume machine memory $m$ satisfies the input-encoding predicate. Then there is a final machine memory $m\prime$ such that the compiled program terminates within its specified $\operatorname{ramSteps}(P,\delta,c)$ execution bound, returns the verdict decoded from $\sigma\prime$ in mode $\delta$, and satisfies the compiler outcome relation.
--
--   Connects every concrete source-level proof to the final word-RAM semantics. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Compiler/WholeProgram.lean#L217-L263

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ThreeSum1960614.Machine.Light.Compiler
end ThreeSum1960614.Machine.Light.Compiler
namespace ThreeSum1960614.Machine.Light.Exec
end ThreeSum1960614.Machine.Light.Exec


namespace Light
end Light
namespace Light.Compiler
end Light.Compiler
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Compiler
end ThreeSum1960614.Machine.Light.Compiler
namespace ThreeSum1960614.Machine.ThreeSumApsp.WordRam
end ThreeSum1960614.Machine.ThreeSumApsp.WordRam
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

open _root_.Light.Compiler
open _root_.ThreeSum1960614.Machine.Light.Compiler

open _root_.EndStatement renaming Instr -> Instr
open _root_.EndStatement renaming exec -> exec
variable {W : ℕ}

theorem ThreeSum1960614.Machine.Light.Compiler.compileProgram_correct {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {p0 : ℕ} {dec : Bool} {μ : ℕ → ℤ}
    {i j : ℤ} {σ' : _root_.ThreeSum1960614.Machine.Light.State} {c : ℕ} {m : ℤ → BitVec W}
    (h : _root_.ThreeSum1960614.Machine.Light.Exec lim P 0 (_root_.ThreeSum1960614.Machine.Light.mainStmt p0) ⟨_root_.Light.frame [0, i, j], μ⟩ σ' c)
    (hfit : _root_.ThreeSum1960614.Machine.Light.Compiler.Fits W lim (_root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec) (_root_.ThreeSum1960614.Machine.Light.Compiler.stackCells P lim)) (hm : _root_.ThreeSum1960614.Machine.Light.Compiler.Input lim μ i j m) :
    ∃ m' : ℤ → BitVec W, _root_.EndStatement.exec (_root_.ThreeSum1960614.Machine.Light.compileProgram P p0 dec) (_root_.ThreeSum1960614.Machine.Light.ramSteps P dec c) 0 m
        = some (_root_.Light.verdictOf dec (σ'.loc 0), m') ∧ _root_.ThreeSum1960614.Machine.Light.Compiler.Outcome lim P dec m σ' m' := by sorry
