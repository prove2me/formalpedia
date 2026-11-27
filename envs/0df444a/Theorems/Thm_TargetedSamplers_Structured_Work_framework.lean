-- Prove2me | Theorems.Thm_TargetedSamplers_Structured_Work_framework
-- name    : TargetedSamplers.Structured.Work.framework
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:00:59.530896+00:00
-- url     : https://prove2.me/theorems/ea312f41-412a-52af-905a-43fd9b1b3c8d
-- title:
--   Exact log-cost execution of structured RAM routines: basic facts
-- statement:
--   Four facts relating structured routines to the published log-cost machine.
--
--   1. If a structured routine $c$ runs from the all-zero store to a store $t$ with exact cost at most $k$, and every jump label of its compiled code has bit length at most $J$, then the compiled program halts with output $t.\mathrm{out}$ and total cost at most $k+1$.
--   2. A step-counted execution of $k$ primitive steps in which every word has at most $b\ge 2$ bits, and every static field has at most $J$ bits, has exact cost at most
--   $$k\,(4b+4J+4).$$
--   3. The static width of the compiled program of $c$ bounds every static field of $c$.
--   4. The field-width bound is monotone in $J$.
--
--   These facts let an algorithm be verified mostly with word-width reasoning while charging exactly the parts whose words are unbounded.
-- source:
--   Engineering lemma for DirectedHamiltonicity.Main.execute_cycle_search (Def_DirectedHamiltonicity_CycleSearch), supporting the formalization of Theorem 1 of T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity (STOC 2027 submission #811), PDF pp. 2-5.

import Definitions.Def_LogCostRAM_WorkExecution

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Work

theorem TargetedSamplers.Structured.Work.framework :
    (∀ {τ : Tapes} {J : ℕ} {c : Cmd} {t : Store} {k : ℕ},
      WExec τ J c ⟨fun _ => 0, []⟩ t k → ((c.compile 0).length).size ≤ J →
      c.program.RunsIn τ (k + 1) (some t.out)) ∧
    (∀ {τ : Tapes} {b J : ℕ} {c : Cmd} {s t : Store} {k : ℕ},
      Exec τ (fun v => v.Fits b) c s t k → s.Fits b → Cmd.FieldsFit J c → 2 ≤ b →
      WExec τ J c s t (k * (4 * b + 4 * J + 4))) ∧
    (∀ (c : Cmd), Cmd.FieldsFit (staticWidth c.program) c) ∧
    (∀ {J J' : ℕ} (c : Cmd), J ≤ J' → Cmd.FieldsFit J c → Cmd.FieldsFit J' c) := by sorry
