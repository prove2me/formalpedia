-- Prove2me | Theorems.Thm_ThreeSumApsp_FromClaims_solvedAt_of_realized
-- name    : ThreeSumApsp.FromClaims.solvedAt_of_realized
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T08:37:58.522457+00:00
-- url     : https://prove2.me/theorems/2ff467bf-fd58-4d33-b7c4-12db26886906
-- title:
--   Converting an eventual realized time bound into the final machine specification
-- statement:
--   Let $Q$ be a problem in the source's final word-RAM specification, let $T(n,u)$ be a realized running-time function, and fix a natural weight exponent $\kappa$. Realization means that an appropriate machine program and word-size slope solve inputs with $U=n^\kappa$ in at most $c\max\{T(n,U),0\}+c$ steps for some $c\ge0$.
--
--   Suppose, for real $C,a$ and natural $e$, that all sufficiently large $n$ satisfy
--
--   $$T(n,n^\kappa)\le Cn^a(\log n)^e.$$
--
--   Then there are a program, word-size slope, and constant $K$ solving every such input in at most $K(n^a(\log n)^e+1)$ steps. This is the final predicate $\operatorname{SolvedInTimeAt}(Q,\kappa,a,e)$, including the finitely many small sizes.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/RunningTimes/FromClaims/Bounds.lean#L88-L109).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/RunningTimes/FromClaims/Bounds.lean#L88-L109

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Realized
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Solving
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSumApsp_Dominated_of_eventually

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSumApsp.FromClaims.solvedAt_of_realized : ∀ {Q : EndStatement.Problem} (T : Nat → Real → Real) (κ : Nat),
  ThreeSumApsp.WordRam.Realized Q T →
    ∀ {C a : Real} {e : Nat},
      @Filter.Eventually.{0} Nat
          (fun (n : Nat) =>
            @LE.le.{0} Real Real.instLE
              (T n
                (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                  (@Nat.cast.{0} Real Real.instNatCast n) (@Nat.cast.{0} Real Real.instNatCast κ)))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                    (@Nat.cast.{0} Real Real.instNatCast n) a)
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                    (Real.log (@Nat.cast.{0} Real Real.instNatCast n)) e))))
          (@Filter.atTop.{0} Nat Nat.instPreorder) →
        ThreeSumApsp.WordRam.SolvedInTimeAt Q κ a e := by
  sorry
