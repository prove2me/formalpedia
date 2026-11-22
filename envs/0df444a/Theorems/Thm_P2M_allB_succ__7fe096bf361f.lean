-- Prove2me | Theorems.Thm_P2M_allB_succ__7fe096bf361f
-- name    : P2M_allB_succ__7fe096bf361f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:48:42.183407+00:00
-- url     : https://prove2.me/theorems/13194702-00b2-481f-88d9-c6b9105fb359
-- title:
--   P2 M all B succ  7fe096bf361f: P2 M all B succ  7fe096bf361f
-- statement:
--   The P2 M all B succ  7fe096bf361f construction uses the P2 M all B succ  7fe096bf361f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L198-L206
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean#L198-L206

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_FourThree_Theory
set_option autoImplicit true
open Finset

theorem P2M_allB_succ__7fe096bf361f (A B c : ℕ) (hc : c.succ.ble (A.add B)) (ha : allA A B c)
    (hB : allB B c) :
    allB B.succ c := by sorry

alias «allB_succ'» := P2M_allB_succ__7fe096bf361f
