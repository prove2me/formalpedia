-- Prove2me | Theorems.Thm_PvsNP_WorkBoundarySplice_splice
-- name    : PvsNP.WorkBoundarySplice.splice
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-27T03:04:52.565778+00:00
-- url     : https://prove2.me/theorems/cace2e17-d7c5-4d83-b116-a7fb8d955754
-- title:
--   Equal crossing records allow splicing two single-tape runs
-- statement:
--   Two finite runs start at a common head position, end with a specified control-state property, and have the same sequence of arrival states across a fixed work-tape boundary. The mixed initial configuration takes the starting-side half-tape from one run and the other half from the other run. Its run reaches the same terminal property with the same crossing record in at most the sum of the two original step counts.
-- source:
--   Formalized crossing-sequence splicing after F. C. Hennie (1965), doi:10.1016/S0019-9958(65)90399-2.

import Definitions.Def_SingleTapeWorkBoundary

set_option autoImplicit false

open PvsNP.WorkBoundarySplice

variable {Q Γ : Type*}

theorem PvsNP.WorkBoundarySplice.splice {M : Machine Q Γ} {cut : ℤ} {accept : Q → Prop}
    {record : List Q} {a b : Config Q Γ} {n m : ℕ}
    (sameHead : a.head = b.head)
    (left : Run M cut accept a record n) (right : Run M cut accept b record m) :
    ∃ k, k ≤ n+m ∧ Run M cut accept (patch cut (rightOf cut a.head) a b) record k := by sorry
