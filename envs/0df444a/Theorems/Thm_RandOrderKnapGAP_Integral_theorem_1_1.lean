-- Prove2me | Theorems.Thm_RandOrderKnapGAP_Integral_theorem_1_1
-- name    : RandOrderKnapGAP.Integral.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:27:41.059927+00:00
-- url     : https://prove2.me/theorems/5cb0874a-137a-447f-8f74-ec0668aa4bb4
-- title:
--   Theorem 1.1, knapsack and GAP clauses — one randomized online algorithm earns at least $0.2564\,\mathrm{OPT}_{\mathrm{int}}$ in random order
-- statement:
--   There is a randomized online algorithm for integral knapsack and GAP satisfying
--   $$\mathbb E[\mathrm{ALG}]\ \ge\ 0.2564\ \mathrm{OPT}_{\mathrm{int}} .$$
--   Precisely: one algorithm, fixed before the instance, such that for every integral GAP instance — every number $n$ of items (in random order) and $m$ of machines, capacities $B_b>0$, arbitrary nonnegative sizes $s_{bi}$ and values $v_{bi}$ — it is feasible on every run and its expected value, over the uniformly random arrival order and its internal randomness, is at least $0.2564$ times the integral offline optimum; and the same algorithm run on any integral knapsack instance (capacity $B>0$, nonnegative sizes and values), as the GAP instance with one machine, is feasible on every run and earns at least $0.2564\,\mathrm{OPT}_{\mathrm{int}}$ in expectation.
--
--   The previous best ratio for both problems was $(1-\ln2)/2\approx0.1534$ (and $1/5.59$ for knapsack); the guarantee is against the integral optimum, for every input length and with no restriction on sizes or values.
--
--   The GPAP clause is stated in the companion item `RandOrderKnapGAP.Integral.theorem_1_1_gpap`. Together the two items cover Theorem 1.1.
--
--   Differences from the source:
--   - reading: Theorem 1.1 as printed has no running-time clause (the proof on p. 72 adds polynomial running time as a remark) → no running-time clause; reason: the printed statement claims only the ratio; a running-time claim would need a machine model the theorem does not state
--   - encoding: a randomized online algorithm that knows n and the capacities, sees each item's data on arrival and decides irrevocably → RandOnlineAlg: its own probability space (Ω, P) fixed with the algorithm; the round-r decision is a function of the public parameter (m and the capacities), n, the arrived items in order with identities and data (current item last) and ω, each fibre measurable in ω; reason: makes the information the algorithm may use explicit; every algorithm of the paper's model is one, and nothing about the order or the future is passed
--   - encoding: E[ALG] over the uniformly random arrival order and the internal randomness → (1/n!) ∑_{π ∈ Perm(Fin n)} ∫ ALG(π, ω) dP(ω), with π r the item of (0-based) round r; reason: the uniform order is the average over the n! permutations; ALG is bounded and measurable, so the integral is the expectation
--   - encoding: the algorithm is feasible (no capacity is exceeded) → Feasible: for every arrival order π, every ω and every machine/resource, the accepted load is at most the capacity; reason: feasibility on every run, as in Lemma C.1's 'Algorithm 5 is feasible'
--   - reading: 'a randomized online algorithm for integral knapsack and GAP' → one GAP algorithm A with both clauses; on knapsack instances it is run as toKnapsack A (the one-machine GAP instance); reason: one algorithm serves both problems, knapsack being GAP with one machine (§5)
--   - encoding: items [n], machines/resources b with capacities B_b > 0, nonnegative sizes and values, OPT_int a maximum → items Fin n, machines Fin m, the standing conditions as structure fields, OPT_int = Finset.sup' over the finite nonempty set of feasible integral solutions; reason: Lean convention; same instances, and the maximum is attained (the empty solution is feasible)
--   - encoding: Theorem 1.1 states the knapsack and GAP guarantee and its GPAP extension → the knapsack and GAP clauses are in theorem_1_1; the GPAP clause is in theorem_1_1_gpap; reason: both items are present in this mission; the split does not omit a clause
-- source:
--   Agrawal, Khan, Pareek, Improved Algorithms in the Random-Order Model: Knapsack, GAP, and Beyond, STOC 2027 submission (manuscript sha256 7825a05f…), p. 2 (PDF 4), Theorem 1.1; proved p. 72 (PDF 74)

import Mathlib
import Definitions.Def_RandOrderKnapGAP_Integral_Instances
import Definitions.Def_RandOrderKnapGAP_Integral_OnlineModel

namespace RandOrderKnapGAP.Integral

/-- **Theorem 1.1** (integral knapsack and GAP), p. 2: there is one randomized online algorithm,
fixed before the instance, which for every integral GAP instance (every `n`, every `m`,
capacities `B_b > 0`, nonnegative sizes and values) is feasible on every run and has
`E[ALG] ≥ 0.2564 · OPT_int`, and which, run on a knapsack instance as a one-machine GAP
instance, is feasible on every run and has `E[ALG] ≥ 0.2564 · OPT_int` of the knapsack. -/
theorem theorem_1_1 :
    ∃ A : GAPAlg,
      (∀ (n m : ℕ) (I : GAPInstance n m),
        GAPAlg.Feasible A I ∧ (0.2564 : ℝ) * I.OPT ≤ GAPAlg.expectedValue A I) ∧
      (∀ (n : ℕ) (I : KnapsackInstance n),
        KnapsackAlg.Feasible (GAPAlg.toKnapsack A) I ∧
          (0.2564 : ℝ) * I.OPT ≤ KnapsackAlg.expectedValue (GAPAlg.toKnapsack A) I) := by sorry

end RandOrderKnapGAP.Integral
