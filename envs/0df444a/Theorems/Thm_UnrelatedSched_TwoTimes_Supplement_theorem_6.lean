-- Prove2me | Theorems.Thm_UnrelatedSched_TwoTimes_Supplement_theorem_6
-- name    : UnrelatedSched.TwoTimes.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:43:41.268748+00:00
-- url     : https://prove2.me/theorems/5e946791-8add-4447-a718-9559e14d09f2
-- title:
--   Theorem 6 — with all $p_{ij}\in\{1,2\}$, one polynomial-time Turing machine returns an optimal schedule
-- statement:
--   The paper states: *the minimum makespan problem on unrelated parallel machines is solvable in polynomial time in the case that all $p_{ij}\in\{1,2\}$.* This is formalized as the existence of a single algorithm, run on a Turing machine with a polynomial bound on its number of steps, that returns an optimal schedule on every such instance.
--
--   An instance consists of $m\ge 1$ machines, $n\ge 0$ jobs and a processing-time matrix $P=(p_{ij})$ with $p_{ij}\in\{1,2\}$ for every machine $i$ and job $j$. A schedule $\sigma$ assigns every job $j$ to one machine $\sigma(j)$; the load of machine $i$ is $\sum_{j:\sigma(j)=i}p_{ij}$ and the makespan $C_{\max}(\sigma)$ is the largest load. Write $\langle m,n,P\rangle$ for the bit-string encoding of the instance and $\langle\sigma\rangle$ for that of the schedule, as in the definition file.
--
--   **Theorem 6.** There are a function $\mathrm{solve}$ from bit strings to bit strings, a multi-stack Turing machine $M$ over the alphabet $\{0,1\}$ and a polynomial $T$ with natural coefficients such that
--
--   1. on every input string $x$, $M$ halts with output $\mathrm{solve}(x)$ within $T(|x|)$ steps;
--   2. for every $m\ge 1$, every $n$ and every $\{1,2\}$ matrix $P$ there is a schedule $\sigma$ with
--
--   $$\mathrm{solve}(\langle m,n,P\rangle)=\langle\sigma\rangle\qquad\text{and}\qquad C_{\max}(\sigma)\le C_{\max}(\tau)\ \text{ for every schedule }\tau .$$
--
--   The machine $M$ and the polynomial $T$ are chosen once, before $m$, $n$ and $P$, so the bound is uniform in the number of machines, the number of jobs and the instance; the number of machines is part of the input and is not fixed. On strings that encode no instance, $\mathrm{solve}$ is unconstrained, but $M$ still halts within $T(|x|)$ steps.
--
--   The result marks the boundary of Section 5: with two processing times $1$ and $2$ the problem is polynomially solvable, while by Theorem 7 (the goal of this mission) every other pair $\{p,q\}$ with $p<q$, $2p\neq q$, is NP-hard.
--
--   **Formalization Note** The computation model is Mathlib's `Turing.TM2ComputableInPolyTime`: a bundled multi-stack Turing machine (finitely many stacks, states and labels) with input and output alphabet `Bool`, together with a polynomial in `Polynomial ℕ` that bounds its number of steps on every input; the theorem asserts that such a machine exists (`Nonempty`). Processing times are natural numbers cast to reals for the published `MatousekLP.Scheduling.makespan` and `IsOptimalSchedule`.
--
--   Differences from the source:
--   - reading: "solvable in polynomial time" → there exist a function solve on bit strings and a Mathlib multi-stack Turing machine computing it within a fixed polynomial number of steps on every input, whose output on each encoded {1,2} instance encodes an optimal schedule; reason: the paper fixes no machine model or encoding; this is the standard meaning (an exact algorithm returning an optimal schedule, polynomial in the input length uniformly in m, n and P), and multi-stack machines simulate the usual models with polynomial overhead.
--   - encoding: the input instance → m and n in unary, then one bit per entry of P in row-major order; the output schedule → each job's machine index in unary; reason: the explicit matrix already has mn entries, so for n ≥ 1 these lengths differ from a binary encoding by a polynomial factor only, and for n = 0 the empty schedule is the only schedule.
--   - encoding: "unrelated parallel machines" → the hypothesis 0 < m; reason: the scheduling domain has at least one machine (§1); with m = 0 and n ≥ 1 no schedule exists, and the excluded instance m = n = 0 is trivial.
--   - encoding: the behaviour on bit strings that encode no instance → unconstrained output, but the same polynomial step bound; reason: the paper's problem has only valid instances as inputs; the machine must still halt on every string, as a total polynomial-time machine does.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 8, §5, Theorem 6, with its proof on p. 8; scheduling model p. 2, §1

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoTimes_Supplement_OneTwoEncoding

open MatousekLP.Scheduling

namespace UnrelatedSched.TwoTimes.Supplement

/-- Theorem 6 (Lenstra, Shmoys, Tardos, CWI Report OS-R8714 (1987), §5, p. 8): the minimum
makespan problem on unrelated parallel machines is solvable in polynomial time when all
`p_ij ∈ {1, 2}`.

There is one function `solve` on bit strings, computed by a single Mathlib multi-stack Turing
machine (`Turing.TM2ComputableInPolyTime`, input and output alphabet `Bool`) within a number of
steps bounded by a fixed polynomial in the input length, such that for every number of machines
`m ≥ 1`, every number of jobs `n` and every matrix `P` with entries in `{1, 2}`, the output on the
encoded instance `encodeInstance P` is the encoding of a schedule `σ` that is optimal for the
processing times `P` (its makespan is at most that of every schedule). The machine and its
polynomial are fixed before `m`, `n` and `P`. On bit strings that encode no `{1, 2}` instance the
output is unconstrained, but the machine still halts within the same polynomial bound. -/
theorem theorem_6 :
    ∃ solve : List Bool → List Bool,
      Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) id solve) ∧
      ∀ (m n : ℕ), 0 < m → ∀ P : Matrix (Fin m) (Fin n) ℕ, IsOneTwoMatrix P →
        ∃ σ : Fin n → Fin m, solve (encodeInstance P) = encodeSchedule σ ∧
          IsOptimalSchedule (fun i j => (P i j : ℝ)) σ := by sorry

end UnrelatedSched.TwoTimes.Supplement
