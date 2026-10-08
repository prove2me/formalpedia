-- Prove2me | Theorems.Thm_ThreeSumApsp_Spec_length_classIdx_eq_card
-- name    : ThreeSumApsp.Spec.length_classIdx_eq_card
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T08:28:27.565267+00:00
-- url     : https://prove2.me/theorems/0c0d3a2d-20b0-455e-aa99-97fbe972f32e
-- title:
--   List and set representations of a residue class have equal size
-- statement:
--   Let $n\in\mathbb N$, $p>0$, and let the integer lists $AB,BC,AC$ specify the three weight arrays of a tripartite instance, using default zero for missing entries. For a residue $\rho\in\{0,\ldots,p-1\}$, let $W_\rho$ be the set of pairs $(a,b)$ with $0\le a,b<n$ and $w_{AB}(a,b)\equiv\rho\pmod p$.
--
--   The implementation's list of row-major positions with this residue has exactly the same size:
--
--   $$\left|\operatorname{classIdx}(n,\operatorname{residList}(p,AB),\rho)\right|=|W_\rho|.$$
--
--   This connects the list-based implementation of Theorem 17 to its set-based chunk count; no length assumption on the input lists is required.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Classes.lean#L29-L46).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Classes.lean#L29-L46

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Chunks
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Hashing
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSumApsp.Spec.length_classIdx_eq_card : ∀ (n : Nat) {p : Nat} (AB BC AC : List.{0} Int),
  @Ne.{1} Nat p (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    ∀ (ϱ : Fin p),
      @Eq.{1} Nat
        (@List.length.{0} Nat (ThreeSumApsp.Spec.classIdx n (ThreeSumApsp.Spec.residList p AB) (@Fin.val p ϱ)))
        (@Finset.card.{0} (Prod.{0, 0} (Fin n) (Fin n))
          (@ThreeSumApsp.TriangleInstance.residueClass n (ThreeSumApsp.Spec.triOf n AB BC AC) p ϱ)) := by
  sorry
