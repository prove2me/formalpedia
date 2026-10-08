-- Prove2me | Theorems.Thm_ThreeSumApsp_Spec_unrank_succ_shape
-- name    : ThreeSumApsp.Spec.unrank_succ_shape
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T07:54:29.266805+00:00
-- url     : https://prove2.me/theorems/0d65a214-8168-4917-ad17-2b87408c5288
-- title:
--   The exact update between consecutive fixed-weight masks
-- statement:
--   Let $L,m,r\in\mathbb N$ with $r+1<\binom Lm$. Let $u_r$ be the length-$L$ Boolean mask returned by the source's unranking enumeration at rank $r$. There are a Boolean prefix $v$ and natural numbers $a,b$ such that
--
--   $$L=|v|+2+a+b,\qquad u_r=v\,10\,0^a1^b,\qquad u_{r+1}=v\,01\,1^b0^a.$$
--
--   Concatenation is written by juxtaposition, and $0,1$ denote false and true. This characterizes the next-mask operation used to enumerate subsets in the implementation of Theorem 5.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Subsets.lean#L180-L217).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Subsets.lean#L180-L217

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Subsets
import Mathlib.Data.Bool.Count
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSumApsp.Spec.unrank_succ_shape : ∀ {L m r : Nat},
  @LT.lt.{0} Nat instLTNat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (L.choose m) →
    ∃ (pre : List.{0} Bool) (a : Nat) (b : Nat),
      And
        (@Eq.{1} Nat L
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Bool pre)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              a)
            b))
        (And
          (@Eq.{1} (List.{0} Bool) (ThreeSumApsp.Spec.unrank L m r)
            (@HAppend.hAppend.{0, 0, 0} (List.{0} Bool) (List.{0} Bool) (List.{0} Bool)
              (@instHAppendOfAppend.{0} (List.{0} Bool) (@List.instAppend.{0} Bool)) pre
              (@List.cons.{0} Bool Bool.true
                (@List.cons.{0} Bool Bool.false
                  (@HAppend.hAppend.{0, 0, 0} (List.{0} Bool) (List.{0} Bool) (List.{0} Bool)
                    (@instHAppendOfAppend.{0} (List.{0} Bool) (@List.instAppend.{0} Bool))
                    (@List.replicate.{0} Bool a Bool.false) (@List.replicate.{0} Bool b Bool.true))))))
          (@Eq.{1} (List.{0} Bool)
            (ThreeSumApsp.Spec.unrank L m
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@HAppend.hAppend.{0, 0, 0} (List.{0} Bool) (List.{0} Bool) (List.{0} Bool)
              (@instHAppendOfAppend.{0} (List.{0} Bool) (@List.instAppend.{0} Bool)) pre
              (@List.cons.{0} Bool Bool.false
                (@List.cons.{0} Bool Bool.true
                  (@HAppend.hAppend.{0, 0, 0} (List.{0} Bool) (List.{0} Bool) (List.{0} Bool)
                    (@instHAppendOfAppend.{0} (List.{0} Bool) (@List.instAppend.{0} Bool))
                    (@List.replicate.{0} Bool b Bool.true) (@List.replicate.{0} Bool a Bool.false))))))) := by
  sorry
