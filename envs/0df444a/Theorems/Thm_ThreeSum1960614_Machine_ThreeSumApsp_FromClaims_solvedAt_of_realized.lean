-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSumApsp_FromClaims_solvedAt_of_realized
-- name    : ThreeSum1960614.Machine.ThreeSumApsp.FromClaims.solvedAt_of_realized
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:13:14.437955+00:00
-- url     : https://prove2.me/theorems/f1b7f56d-c310-4c67-b669-c67204eba4be
-- title:
--   A realized time bound yields a solved-at exponent
-- statement:
--   Let $Q$ be a benchmark problem and let real-valued time model $T$ be realized on the word RAM. If, for natural $\kappa,e$ and real $C,a$, eventually $$T(n,n^\kappa)\le Cn^a(\log n)^e,$$ then $Q$ satisfies the formal solved-at predicate with input-value exponent $\kappa$, size exponent $a$, and logarithmic exponent $e$.
--
--   This implication transfers a realized machine time with logarithmic overhead to the formal solved-at statement.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/RunningTimes/FromClaims/Bounds.lean#L88-L109

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Solving
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Ceil
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_ThreeSum1960614_Machine_Bundle002
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
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

namespace ThreeSum1960614.Machine.ThreeSumApsp.Dominated
end ThreeSum1960614.Machine.ThreeSumApsp.Dominated


namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSum1960614.Machine.ThreeSumApsp.FromClaims
end ThreeSum1960614.Machine.ThreeSumApsp.FromClaims
namespace ThreeSum1960614.Machine.ThreeSumApsp.WordRam
end ThreeSum1960614.Machine.ThreeSumApsp.WordRam
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.FromClaims
end ThreeSumApsp.FromClaims
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp

open _root_.ThreeSum1960614.Machine.ThreeSumApsp.FromClaims

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam
open _root_.EndStatement renaming Instr -> Instr

theorem ThreeSum1960614.Machine.ThreeSumApsp.FromClaims.solvedAt_of_realized {Q : _root_.EndStatement.Problem} (T : ℕ → ℝ → ℝ) (κ : ℕ)
    (hR : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Realized Q T) {C a : ℝ} {e : ℕ}
    (hev : ∀ᶠ n : ℕ in Filter.atTop,
      T n ((n : ℝ) ^ ((κ : ℕ) : ℝ)) ≤ C * ((n : ℝ) ^ a * Real.log n ^ e)) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.SolvedInTimeAt Q κ a e := by sorry
