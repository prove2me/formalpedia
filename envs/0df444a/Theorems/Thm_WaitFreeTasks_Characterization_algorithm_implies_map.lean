-- Prove2me | Theorems.Thm_WaitFreeTasks_Characterization_algorithm_implies_map
-- name    : WaitFreeTasks.Characterization.algorithm_implies_map
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:30:27.716242+00:00
-- url     : https://prove2.me/theorems/f4553980-5815-4e46-abbb-da37e69b62d1
-- title:
--   Lemma 17 — Wait-free algorithm implies a PL finite-to-one map
-- statement:
--   Let $T=(I,O,\Delta)$ be a chromatic task for any $n\ge2$ in the asynchronous read/write model. If an actual deterministic wait-free protocol solves $T$, then
--
--   $$\exists f:|I|\to|O|,\quad f\text{ is PL and finite-to-one},\qquad f(|\sigma|)\subseteq|\Delta(\sigma)|\quad(\sigma\in I).$$
--
--   Every fiber over every output point is finite. The geometric map is produced by the theorem; it is not preselected or included in the protocol. The operational premise quantifies over arbitrary schedules and crash patterns.
--
--   Differences from the source:
--   - encoding: maps between finite complex realizations → ambient real coordinate functions restricted to the realizations, with faces stored as finite sets; reason: every real barycentric point is included; values off the realizations are irrelevant and extend arbitrarily
--   - encoding: identifiers in [n] = {1,...,n} → identifiers in Fin n = {0,...,n-1}; reason: subtracting one is an order preserving bijection; all n >= 2 remain quantified
--   - encoding: deterministic asynchronous read/write wait-free solvability → existence of atomic transition tables with correctness at every prefix and termination for infinitely scheduled participants; reason: this expresses the source state-machine model over arbitrary schedules without a fairness premise or a geometric certificate
-- source:
--   Hagit Attiya, Ami Paz, STOC 2027 submission #828 (October 2026), p. 18 (PDF p. 20), Lemma 17

import Definitions.Def_WaitFreeTasks_Characterization_SharedMemory

set_option autoImplicit false

open Classical

namespace WaitFreeTasks.Characterization

/-- **Lemma 17** (Attiya–Paz, STOC 2027 submission #828 (October 2026), printed p. 18, PDF p. 20). Given a chromatic task `(I, O, Δ)` for
`n ≥ 2` processes, if the task is wait-free solvable in the asynchronous read/write shared-memory
model, then there is a PL map `f : |I| → |O|` that is carried by `Δ` and is finite-to-one. -/
theorem algorithm_implies_map {n : ℕ} {VI VO : Type} (hn : 2 ≤ n) (T : Task n VI VO)
    (hsolv : WaitFreeSolvable T) :
    ∃ f : (VI → ℝ) → (VO → ℝ), IsPL T.I.real f ∧ IsCarried T f ∧
      FiniteToOne T.I.real T.O.real f := by sorry

end WaitFreeTasks.Characterization
