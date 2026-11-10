-- Prove2me | Theorems.Thm_RandOrderKnapGAP_Integral_theorem_1_1_gpap
-- name    : RandOrderKnapGAP.Integral.theorem_1_1_gpap
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:27:39.00622+00:00
-- url     : https://prove2.me/theorems/89fac0e4-d48c-43af-8c19-75476c655ef0
-- title:
--   Theorem 1.1, GPAP clause — the $0.2564$ guarantee for integral GPAP under resource deletion
-- statement:
--   There is a randomized online algorithm, fixed before the instance, such that for every GPAP instance — every number $n$ of items and $m$ of resources, capacities $B_b>0$, finite action sets with nonnegative values and consumptions and a rejection action, satisfying the resource-deletion property — the algorithm is feasible on every run and
--   $$\mathbb E[\mathrm{ALG}]\ \ge\ 0.2564\ \mathrm{OPT}_{\mathrm{int}} ,$$
--   the expectation over the uniformly random arrival order and the algorithm's internal randomness.
--
--   The guarantee holds with no loss depending on the number of resources an action uses; with §5 it contains the knapsack and GAP clauses of Theorem 1.1.
--
--   Differences from the source:
--   - reading: Theorem 1.1 as printed has no running-time clause (the proof on p. 72 adds polynomial running time as a remark) → no running-time clause; reason: the printed statement claims only the ratio; a running-time claim would need a machine model the theorem does not state
--   - encoding: a randomized online algorithm that knows n and the capacities, sees each item's data on arrival and decides irrevocably → RandOnlineAlg: its own probability space (Ω, P) fixed with the algorithm; the round-r decision is a function of the public parameter (m and the capacities), n, the arrived items in order with identities and data (current item last) and ω, each fibre measurable in ω; reason: makes the information the algorithm may use explicit; every algorithm of the paper's model is one, and nothing about the order or the future is passed
--   - encoding: E[ALG] over the uniformly random arrival order and the internal randomness → (1/n!) ∑_{π ∈ Perm(Fin n)} ∫ ALG(π, ω) dP(ω), with π r the item of (0-based) round r; reason: the uniform order is the average over the n! permutations; ALG is bounded and measurable, so the integral is the expectation
--   - encoding: the algorithm is feasible (no capacity is exceeded) → Feasible: for every arrival order π, every ω and every machine/resource, the accepted load is at most the capacity; reason: feasibility on every run, as in Lemma C.1's 'Algorithm 5 is feasible'
--   - encoding: GPAP instance: a multiple-choice packing instance with the resource-deletion property → GPAPInstance with the hypothesis I.ResourceDeletion (a Prop: w and D exist; the algorithm sees only actions, values and consumptions); the decision is an action index, an index outside A_i executed as rejection; reason: GPAP instances are exactly those with the property; an algorithm can output the rejection index itself
--   - encoding: items [n], machines/resources b with capacities B_b > 0, nonnegative sizes and values, OPT_int a maximum → items Fin n, machines Fin m, the standing conditions as structure fields, OPT_int = Finset.sup' over the finite nonempty set of feasible integral solutions; reason: Lean convention; same instances, and the maximum is attained (the empty solution is feasible)
-- source:
--   Agrawal, Khan, Pareek, Improved Algorithms in the Random-Order Model: Knapsack, GAP, and Beyond, STOC 2027 submission (manuscript sha256 7825a05f…), p. 2 (PDF 4), Theorem 1.1, second sentence; proved p. 72 (PDF 74)

import Mathlib
import Definitions.Def_RandOrderKnapGAP_Integral_Instances
import Definitions.Def_RandOrderKnapGAP_Integral_OnlineModel

namespace RandOrderKnapGAP.Integral

/-- **Theorem 1.1, GPAP clause**, p. 2: there is one randomized online algorithm, fixed before
the instance, which on every GPAP instance (every multiple-choice packing instance with the
resource-deletion property, Definition 5.1) is feasible on every run and has
`E[ALG] ≥ 0.2564 · OPT_int`. -/
theorem theorem_1_1_gpap :
    ∃ A : GPAPAlg, ∀ (n m : ℕ) (I : GPAPInstance n m), I.ResourceDeletion →
      GPAPAlg.Feasible A I ∧ (0.2564 : ℝ) * I.OPT ≤ GPAPAlg.expectedValue A I := by sorry

end RandOrderKnapGAP.Integral
