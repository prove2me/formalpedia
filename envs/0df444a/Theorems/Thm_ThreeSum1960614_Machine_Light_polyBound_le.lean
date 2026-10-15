-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_Light_polyBound_le
-- name    : ThreeSum1960614.Machine.Light.polyBound_le
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:09:27.931984+00:00
-- url     : https://prove2.me/theorems/a86d875b-bda2-4f4c-8a9a-64599b32029f
-- title:
--   Admissibility bounds polynomial parameters by the word range
-- statement:
--   Suppose parameter list $v$ and width $W$ satisfy word-RAM admissibility with constant $b$, $|v|\le r$, and $s+kr+k\le b$. Then $$\operatorname{polyBound}(s,k,v)\le2^W.$$
--
--   This finite bound translates admissible machine parameters into the numerical polynomial envelope used by the compiler.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/WordSize.lean#L54-L68

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_ThreeSum1960614_Machine_Bundle002
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
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
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSumApsp.WordRam
end ThreeSum1960614.Machine.ThreeSumApsp.WordRam
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

theorem ThreeSum1960614.Machine.Light.polyBound_le {b W s k r : ℕ} {params : List ℕ} (h : _root_.ThreeSumApsp.WordRam.Admissible b params W)
    (hr : params.length ≤ r) (hb : s + k * r + k ≤ b) : _root_.Light.polyBound s k params ≤ 2 ^ W := by sorry
