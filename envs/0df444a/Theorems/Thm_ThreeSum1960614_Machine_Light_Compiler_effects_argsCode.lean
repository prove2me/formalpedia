-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_Light_Compiler_effects_argsCode
-- name    : ThreeSum1960614.Machine.Light.Compiler.effects_argsCode
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:09:17.347985+00:00
-- url     : https://prove2.me/theorems/95a99800-4ad5-4ea2-a56a-1001391e517e
-- title:
--   Effects of compiling call arguments
-- statement:
--   Let a $W$-bit machine memory represent a framed Light state $\sigma$ under compiler size data $Z$. Let $e_0,\ldots,e_{r-1}$ be expressions of width at most the frame width $F$, each safe in $\sigma$. If $k+r\le F+1$, compiling them into temporaries starting at $k$ stores the word encoding of $e_i(\sigma)$ in $T_{k+i}$ for each $i<r$, and preserves memory outside the designated temporary set.
--
--   Connects argument-expression code to the values needed by a simulated procedure call. This is a supporting lemma in the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Compiler/CallFrames.lean#L36-L58

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
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

variable {W : ℕ} {Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W} {σ : _root_.ThreeSum1960614.Machine.Light.State} {q : ℕ} {m : ℤ → BitVec W}

theorem ThreeSum1960614.Machine.Light.Compiler.effects_argsCode (I : _root_.ThreeSum1960614.Machine.Light.Compiler.Framed Z σ q m) (es : List _root_.ThreeSum1960614.Machine.Light.Expr) (k : ℕ)
    (hw : ∀ e ∈ es, e.width ≤ Z.F) (hs : ∀ e ∈ es, e.Safe Z.lim σ)
    (hk : k + es.length ≤ Z.F + 1) :
    (∀ i < es.length,
        _root_.ThreeSumApsp.WordRam.effects (_root_.ThreeSum1960614.Machine.Light.Compiler.argsCode es k) m (_root_.Light.Compiler.cT (k + i)) = _root_.ThreeSumApsp.WordRam.wd W (_root_.Light.frame (es.map (·.val σ)) i)) ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.Light.Compiler.Temps k Z.F) m (_root_.ThreeSumApsp.WordRam.effects (_root_.ThreeSum1960614.Machine.Light.Compiler.argsCode es k) m) := by sorry
