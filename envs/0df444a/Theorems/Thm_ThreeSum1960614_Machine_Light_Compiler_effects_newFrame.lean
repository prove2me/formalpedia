-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_Light_Compiler_effects_newFrame
-- name    : ThreeSum1960614.Machine.Light.Compiler.effects_newFrame
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:09:47.389666+00:00
-- url     : https://prove2.me/theorems/e9eaefe0-d2df-4f1f-baa9-497c83159b44
-- title:
--   Effects of constructing a new call frame
-- statement:
--   Let the machine memory represent a framed Light state with frame base $q$ and width $F$. Suppose the next full frame fits in the stack, the argument values already occupy the designated temporaries, and the return address is at most the dispatcher bound. Executing the new-frame instruction effects produces the argument frame at $q+F+1$, stores the return address at stack cell $q+F$, and preserves memory outside the specified writable region.
--
--   Provides the memory relation needed to simulate procedure entry. This is a supporting lemma in the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Compiler/CallFrames.lean#L100-L149

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

theorem ThreeSum1960614.Machine.Light.Compiler.effects_newFrame (I : _root_.ThreeSum1960614.Machine.Light.Compiler.Framed Z σ q m) (hQ : q + Z.F + 1 + Z.F ≤ Z.Q) (args : List _root_.ThreeSum1960614.Machine.Light.Expr)
    (hargs : ∀ i < args.length, m (_root_.Light.Compiler.cT i) = _root_.ThreeSumApsp.WordRam.wd W (_root_.Light.frame (args.map (·.val σ)) i)) {ret : ℕ}
    (hret : ret ≤ Z.disp) :
    _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z ⟨_root_.Light.frame (args.map (·.val σ)), σ.mem⟩ (q + Z.F + 1)
        (_root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.newFrame Z.F args.length ret) m) ∧
      _root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.newFrame Z.F args.length ret) m (_root_.Light.Compiler.cStack (q + Z.F)) = _root_.ThreeSumApsp.WordRam.wd W ret ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.ThreeSum1960614.Machine.Light.Compiler.Writable Z (q + Z.F)) m (_root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.newFrame Z.F args.length ret) m) := by sorry
