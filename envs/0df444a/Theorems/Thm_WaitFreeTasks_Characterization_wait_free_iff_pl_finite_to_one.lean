-- Prove2me | Theorems.Thm_WaitFreeTasks_Characterization_wait_free_iff_pl_finite_to_one
-- name    : WaitFreeTasks.Characterization.wait_free_iff_pl_finite_to_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:30:47.981084+00:00
-- url     : https://prove2.me/theorems/e89a5819-9aba-44d9-ae27-8ccd9a0435b8
-- title:
--   Theorem 1 — Wait-free solvability via PL finite-to-one maps
-- statement:
--   Let $n\ge2$ and let $T=(I,O,\Delta)$ be a finite chromatic task as in Sections 2.1–2.3. Processes have distinct identifiers, local inputs, unrestricted private memory and computation, and exactly $n$ atomic single-writer multiple-reader registers with fixed initial contents. Then
--
--   $$T\text{ is wait-free solvable}\quad\Longleftrightarrow\quad\exists f:|I|\to|O|,\ f\text{ is PL and finite-to-one and carried by }\Delta.$$
--
--   Carried means $f(|\sigma|)\subseteq|\Delta(\sigma)|$ for every original input simplex. Finite-to-one means every point fiber is finite. PL uses the source's local conical neighborhoods on full real realizations. Solvability means existence of a state-machine protocol correct on every decision prefix of every schedule, terminating for each process that continues to take steps. Neither global purity of $I,O$ nor full participation is required. Both implications are included, for every process count in the source domain.
--
--   Differences from the source:
--   - encoding: maps between finite complex realizations → ambient real coordinate functions restricted to the realizations, with faces stored as finite sets; reason: every real barycentric point is included; values off the realizations are irrelevant and extend arbitrarily
--   - encoding: identifiers in [n] = {1,...,n} → identifiers in Fin n = {0,...,n-1}; reason: subtracting one is an order preserving bijection; all n >= 2 remain quantified
--   - encoding: deterministic asynchronous read/write wait-free solvability → existence of atomic transition tables with correctness at every prefix and termination for infinitely scheduled participants; reason: this expresses the source state-machine model over arbitrary schedules without a fairness premise or a geometric certificate
-- source:
--   Hagit Attiya, Ami Paz, STOC 2027 submission #828 (October 2026), p. 8 (PDF p. 10), Theorem 1

import Definitions.Def_WaitFreeTasks_Characterization_SharedMemory

set_option autoImplicit false

open Classical

namespace WaitFreeTasks.Characterization

/-- **Theorem 1** (Attiya–Paz, STOC 2027 submission #828 (October 2026), printed p. 8, PDF p. 10; also printed p. 2, PDF p. 4). A chromatic
task `(I, O, Δ)` for `n ≥ 2` processes is wait-free solvable in the asynchronous read/write
shared-memory model if and only if there exists a PL finite-to-one map `f : |I| → |O|` that is
carried by `Δ`. -/
theorem wait_free_iff_pl_finite_to_one {n : ℕ} {VI VO : Type} (hn : 2 ≤ n)
    (T : Task n VI VO) :
    WaitFreeSolvable T ↔ ∃ f : (VI → ℝ) → (VO → ℝ), IsPL T.I.real f ∧ IsCarried T f ∧
      FiniteToOne T.I.real T.O.real f := by sorry

end WaitFreeTasks.Characterization
