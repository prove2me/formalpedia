-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_Light_Compiler_steps_setVar
-- name    : ThreeSum1960614.Machine.Light.Compiler.steps_setVar
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:09:34.826992+00:00
-- url     : https://prove2.me/theorems/0479ee2d-cd0f-43b3-b4f4-a4c3060f46f8
-- title:
--   Two instructions implement a local-variable write
-- statement:
--   Let a machine memory represent a framed Light state $\sigma$ at frame $q$, and let $x<F$ be a local index. Suppose the code at position $p$ is the prescribed address-subtraction followed by a store from cell $c$, with $c$ different from the address scratch cell and holding the word encoding of $v\in\mathbb Z$. There is a two-step execution to position $p+2$ representing $\sigma[x\leftarrow v]$, preserving memory outside the frame's writable region.
--
--   Links the concrete store sequence to a source-level assignment. This is a supporting lemma in the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L312-L331

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
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
variable {W : ℕ} {Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W} {F : ℕ}
open _root_.Light.Compiler
open _root_.ThreeSum1960614.Machine.Light.Compiler

variable {σ : _root_.ThreeSum1960614.Machine.Light.State} {q pos : ℕ} {m m' : ℤ → BitVec W} {code rest : List _root_.EndStatement.Instr}

theorem ThreeSum1960614.Machine.Light.Compiler.steps_setVar {x : ℕ} {c v : ℤ} (I : _root_.ThreeSum1960614.Machine.Light.Compiler.Framed Z σ q m) (hx : x < Z.F)
    (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code pos (_root_.EndStatement.Instr.sub _root_.Light.Compiler.cADDR _root_.Light.Compiler.cFP (_root_.Light.Compiler.cPool (2 * x)) :: _root_.EndStatement.Instr.store _root_.Light.Compiler.cADDR c :: rest))
    (hc : m c = _root_.ThreeSumApsp.WordRam.wd W v) (hne : c ≠ _root_.Light.Compiler.cADDR) :
    ∃ m', _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps code 2 ⟨pos, m⟩ ⟨pos + 2, m'⟩ ∧
      _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z { σ with loc := Function.update σ.loc x v } q m' ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.ThreeSum1960614.Machine.Light.Compiler.Writable Z q) m m' := by sorry
