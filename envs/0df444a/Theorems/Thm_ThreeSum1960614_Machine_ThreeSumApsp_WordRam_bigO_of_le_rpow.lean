-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSumApsp_WordRam_bigO_of_le_rpow
-- name    : ThreeSum1960614.Machine.ThreeSumApsp.WordRam.bigO_of_le_rpow
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:13:07.187443+00:00
-- url     : https://prove2.me/theorems/c5637ce1-95ed-4239-95b2-726fa1b8e023
-- title:
--   A real power estimate implies benchmark Big O
-- statement:
--   Let $T:\mathbb N\to\mathbb N$, $C\in\mathbb R$, and nonnegative rational $r$. If $T(n)\le Cn^r$ for every $n\ge2$, then $T$ satisfies the benchmark predicate $\operatorname{BigO}(T,r)$.
--
--   This conversion closes the benchmark Big O predicate after the actual machine time has been bounded by a real power.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Statements/Exponents.lean#L37-L50

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_ThreeSum1960614_Machine_Bundle002
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Function
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
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

namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSum1960614.Machine.ThreeSumApsp.WordRam
end ThreeSum1960614.Machine.ThreeSumApsp.WordRam
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

theorem ThreeSum1960614.Machine.ThreeSumApsp.WordRam.bigO_of_le_rpow {C : ℝ} {r : ℚ} (hr0 : 0 ≤ r) {T : ℕ → ℕ}
    (hT : ∀ n : ℕ, 2 ≤ n → (T n : ℝ) ≤ C * (n : ℝ) ^ (r : ℝ)) : _root_.EndStatement.BigO T r := by sorry
