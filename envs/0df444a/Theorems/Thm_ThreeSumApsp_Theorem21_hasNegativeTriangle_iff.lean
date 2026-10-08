-- Prove2me | Theorems.Thm_ThreeSumApsp_Theorem21_hasNegativeTriangle_iff
-- name    : ThreeSumApsp.Theorem21.hasNegativeTriangle_iff
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T08:22:41.809665+00:00
-- url     : https://prove2.me/theorems/cfe696e7-149d-43bd-b672-a46da3782b4c
-- title:
--   Detecting negative triangles through binary-prefix exact triangles
-- statement:
--   Let $T$ be a tripartite graph with $n$ vertices in each part and integer edge weights in $[-U,U]$. Suppose $3U<2^L$. For each $\ell<L$ and $e\in\{2,3\}$, replace its three kinds of edge weights by
--
--   $$w_{AB}\mapsto\left\lfloor\frac{2(w_{AB}+U)}{2^\ell}\right\rfloor,\quad
--   w_{BC}\mapsto\left\lfloor\frac{2(w_{BC}+U)}{2^\ell}\right\rfloor,\quad
--   w_{AC}\mapsto e-\left\lfloor\frac{2(2U-w_{AC})}{2^\ell}\right\rfloor.$$
--
--   The original graph has a negative-weight triangle if and only if at least one of these $2L$ graphs has a zero-weight triangle. This is the binary-prefix reduction used in Theorem 21(b).
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Theorem21b/NegativeTriangle.lean#L150-L168).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Theorem21b/NegativeTriangle.lean#L150-L168

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Theorem21b_NegativeTriangle
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSumApsp.Theorem21.hasNegativeTriangle_iff : ∀ {n U L : Nat} (T : ThreeSumApsp.TriangleInstance Int n),
  @ThreeSumApsp.TriangleInstance.WeightsBoundedBy Int instLatticeInt Int.instAddGroup n T
      (@Nat.cast.{0} Int instNatCastInt U) →
    @LT.lt.{0} Nat instLTNat
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) U)
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L) →
      Iff
        (@ThreeSumApsp.TriangleInstance.HasNegativeTriangle Int Int.instAdd
          (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)) Int.instLTInt n T)
        (∃ (ℓ : Nat),
          And (@LT.lt.{0} Nat instLTNat ℓ L)
            (∃ (e : Int),
              And
                (Or (@Eq.{1} Int e (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))
                  (@Eq.{1} Int e (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3)))))
                (@ThreeSumApsp.TriangleInstance.HasZeroTriangle Int Int.instAdd
                  (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)) n
                  (@ThreeSumApsp.TriangleInstance.mapWeights n T (ThreeSumApsp.Theorem21.negToExact U ℓ e))))) := by
  sorry
