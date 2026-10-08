-- Prove2me | Theorems.Thm_ThreeSumApsp_TriangleInstance_card_instanceIndices
-- name    : ThreeSumApsp.TriangleInstance.card_instanceIndices
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T08:28:19.910109+00:00
-- url     : https://prove2.me/theorems/134a8059-50b8-49d9-a9e4-02f03112b6fb
-- title:
--   The reduction creates one instance per chunk and vertex piece
-- statement:
--   For an integer-weighted tripartite instance $T$ with $n$ vertices per part and natural parameters $D,g,p$, let $C_\rho$ be the number of chunks of the residue class $W_\rho$, and let $h=\operatorname{numPieces}(n,D,g)$ be the number of pieces in the third vertex part. The source's reduction instances are indexed by triples $(\rho,j,k)$ with $j<C_\rho$ and $k<h$. Their exact number is
--
--   $$|\operatorname{instanceIndices}(T,D,g,p)|=\operatorname{totalChunks}(T,D,p)\,h
--   =\left(\sum_{\rho<p}C_\rho\right)h.$$
--
--   This identity is the counting step in Theorem 17; it requires no additional positivity assumptions on the parameters.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Theorem17/Instances.lean#L335-L348).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Theorem17/Instances.lean#L335-L348

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Parameters
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSumApsp.TriangleInstance.card_instanceIndices : ∀ {n : Nat} (T : ThreeSumApsp.TriangleInstance Int n) (D g p : Nat),
  @Eq.{1} Nat
    (@Finset.card.{0} (ThreeSumApsp.InstanceIndex p) (@ThreeSumApsp.TriangleInstance.instanceIndices n T D g p))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@ThreeSumApsp.TriangleInstance.totalChunks n T D p) (ThreeSumApsp.numPieces n D g)) := by
  sorry
