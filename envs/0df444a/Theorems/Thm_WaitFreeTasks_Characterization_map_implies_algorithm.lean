-- Prove2me | Theorems.Thm_WaitFreeTasks_Characterization_map_implies_algorithm
-- name    : WaitFreeTasks.Characterization.map_implies_algorithm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:30:45.837552+00:00
-- url     : https://prove2.me/theorems/2fedc01a-7450-4412-84c6-d1d1cadadde1
-- title:
--   Lemma 16 — PL finite-to-one map implies a wait-free algorithm
-- statement:
--   Let $T=(I,O,\Delta)$ be a chromatic task for any $n\ge2$ in the source model. If $f:|I|\to|O|$ is PL, carried by $\Delta$, and finite-to-one, then
--
--   $$T\text{ is wait-free solvable}.$$
--
--   Solvability existentially quantifies a deterministic state-machine protocol using exactly $n$ atomic single-writer multiple-reader registers, with fixed initial contents. Correctness holds for every legal input and every finite decision prefix; every process with infinitely many opportunities decides in finite time. Other processes may stop forever. The conclusion contains no assumed asynchronous computability theorem or geometric certificate.
--
--   Differences from the source:
--   - encoding: maps between finite complex realizations → ambient real coordinate functions restricted to the realizations, with faces stored as finite sets; reason: every real barycentric point is included; values off the realizations are irrelevant and extend arbitrarily
--   - encoding: identifiers in [n] = {1,...,n} → identifiers in Fin n = {0,...,n-1}; reason: subtracting one is an order preserving bijection; all n >= 2 remain quantified
--   - encoding: deterministic asynchronous read/write wait-free solvability → existence of atomic transition tables with correctness at every prefix and termination for infinitely scheduled participants; reason: this expresses the source state-machine model over arbitrary schedules without a fairness premise or a geometric certificate
-- source:
--   Hagit Attiya, Ami Paz, STOC 2027 submission #828 (October 2026), p. 18 (PDF p. 20), Lemma 16

import Definitions.Def_WaitFreeTasks_Characterization_SharedMemory

set_option autoImplicit false

open Classical

namespace WaitFreeTasks.Characterization

/-- **Lemma 16** (Attiya–Paz, STOC 2027 submission #828 (October 2026), printed p. 18, PDF p. 20). Given a chromatic task `(I, O, Δ)` for
`n ≥ 2` processes, if there is a PL map `f : |I| → |O|` that is carried by `Δ` and is
finite-to-one, then the task is wait-free solvable in the asynchronous read/write
shared-memory model. -/
theorem map_implies_algorithm {n : ℕ} {VI VO : Type} (hn : 2 ≤ n) (T : Task n VI VO)
    (f : (VI → ℝ) → (VO → ℝ)) (hPL : IsPL T.I.real f) (hcar : IsCarried T f)
    (hfin : FiniteToOne T.I.real T.O.real f) :
    WaitFreeSolvable T := by sorry

end WaitFreeTasks.Characterization
