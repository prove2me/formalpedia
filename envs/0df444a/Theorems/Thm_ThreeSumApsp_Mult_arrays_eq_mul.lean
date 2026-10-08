-- Prove2me | Theorems.Thm_ThreeSumApsp_Mult_arrays_eq_mul
-- name    : ThreeSumApsp.Mult_arrays_eq_mul
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T08:22:53.144314+00:00
-- url     : https://prove2.me/theorems/19636cd0-2174-4b80-8e8b-5dd21fb5a198
-- title:
--   The encoded multiplication computes each matrix product entry
-- statement:
--   Fix $L,m\in\mathbb N$. For every set $Q\subseteq\{0,\ldots,L-1\}$, let $X_Q$ and $Y_Q$ be integer matrices of sizes $3^{L-m}\times4^m$ and $4^m\times3^{L-m}$. The source packs these families into arrays $a=\operatorname{arrayL}(m,X)$ and $b=\operatorname{arrayR}(m,Y)$, indexed by left and right variable strings.
--
--   For $|Q|=m$ and row and column strings $r,c\in\{0,1,2\}^{L-m}$,
--
--   $$\operatorname{Mult}(a,b)[\operatorname{outStrOf}(Q,r,c)]=(X_QY_Q)_{r,c}.$$
--
--   Here the output string records the inner positions $Q$ and the outer row and column. This is the entrywise form of Lemma 9, which identifies one encoded multiplication with all the matrix products at once.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec2/Lemma9.lean#L179-L205).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec2/Lemma9.lean#L179-L205

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Levels
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSumApsp.Mult_arrays_eq_mul : ∀ {L m : Nat} (X : Finset.{0} (Fin L) → ThreeSumApsp.LeftMat L m) (Y : Finset.{0} (Fin L) → ThreeSumApsp.RightMat L m)
  (Q : Finset.{0} (Fin L)) (hQ : @Eq.{1} Nat (@Finset.card.{0} (Fin L) Q) m) (r c : ThreeSumApsp.OuterStr L m),
  @Eq.{1} Int
    (@ThreeSumApsp.Mult L (@ThreeSumApsp.arrayL L m X) (@ThreeSumApsp.arrayR L m Y)
      (@ThreeSumApsp.outStrOf L m Q hQ r c))
    (@HMul.hMul.{0, 0, 0} (ThreeSumApsp.LeftMat L m) (ThreeSumApsp.RightMat L m)
      (Matrix.{0, 0, 0} (ThreeSumApsp.OuterStr L m) (ThreeSumApsp.OuterStr L m) Int)
      (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (ThreeSumApsp.OuterStr L m) (ThreeSumApsp.InnerStr m)
        (ThreeSumApsp.OuterStr L m) Int
        (@Pi.instFintype.{0, 0} (Fin m)
          (fun (a : Fin m) =>
            Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (instDecidableEqFin m) (Fin.fintype m) fun (a : Fin m) =>
          @instFintypeProd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        Int.instMul Int.instAddCommMonoid)
      (X Q) (Y Q) r c) := by
  sorry
