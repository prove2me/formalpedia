-- Prove2me | Theorems.Thm_PvsNP_OnlineRegionRead_exact_two_phase_record
-- name    : PvsNP.OnlineRegionRead.exact_two_phase_record
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-27T04:44:13.60265+00:00
-- url     : https://prove2.me/theorems/3cd7a48d-1185-4e37-8bb7-d204a9742798
-- title:
--   A two-phase run yields a crossing record that certifies splicing
-- statement:
--   Split a one-way input run into two consecutive parts governed by two work-cell ownership masks. The run has a record whose length is the sum of its ownership changes in the two parts plus two. The record determines the owner of every actual input read. Any other execution with that same record and aligned initial control, head and input index has a joint trace certificate for splicing.
-- source:
--   One-way crossing sequence method, Kalyanasundaram and Schnitger, DOI 10.1007/978-3-322-95233-2_15.

import Definitions.Def_OnlineExecutionLog

set_option autoImplicit false
set_option maxHeartbeats 3000000

open PvsNP.OnlineRegionRead

theorem PvsNP.OnlineRegionRead.exact_two_phase_record
    {Q Γ : Type} {M : Program Q Γ} {word : Word} {mask : Bool → ℤ → Bool}
    (strip : List ℤ) (covered : ∀ p, mask false p ≠ mask true p → p ∈ strip)
    {a mid z : Cursor Q Γ} {n m c d : ℕ} {p q : List (ℕ × Bool)}
    (first : CountedRun M word (mask false) a mid n c p)
    (second : CountedRun M word (mask true) mid z m d q) :
    ∃ log, Logged M word mask strip false a log z ∧ log.length = c+d+2 ∧
      (∀ item ∈ p ++ q, routeFrom log item.1 = item.2) ∧
      ∀ {other : Word} {b b' : Cursor Q Γ},
        Logged M other mask strip false b log b' → Aligned a b →
        ∃ last : Bool, JointTrace M word other (routeFrom log) (mask false) a b (mask last) z b' := by sorry
