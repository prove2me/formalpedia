-- Prove2me | Theorems.Thm_VecKnapsackMitM_Main_lemma_4_6
-- name    : VecKnapsackMitM.Main.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:36:15.316748+00:00
-- url     : https://prove2.me/theorems/e49e9251-306a-41af-8b66-ec903eef74d2
-- title:
--   Lemma 4.6 — Algorithm 3 is a $(1-\varepsilon)$-approximation for $\varepsilon\le(d-1)/d$
-- statement:
--   For every integer $d\ge2$, $\rho\in(0,1)$ and $\varepsilon\in(0,\frac{d-1}{d}]$, Algorithm 3 is a $(1-\varepsilon)$-approximation algorithm for $d$-Knapsack: on every instance (nonnegative profits, weights, capacities), every set $S$ that Algorithm 3 can return — for every order of non-increasing profit chosen in Line 1, every family of representative solutions with the guarantees of Lemma 4.2 for $\delta=\varepsilon^2\rho/(2(d-1))$, every correct answer of each range query and every iteration order of Line 6 — is feasible and has $p(S)\ge(1-\varepsilon)\,\mathrm{OPT}$.
--
--   Differences from the source:
--   - encoding: items I = {1, …, n} and dimensions t ∈ {1, …, d} → items Fin n (the paper's item i+1 is i) and dimensions Fin d (the paper's dimension t+1 is t: w̄_1 is t = 0, w̄_d is t = d − 1, the middle dimensions 2, …, d − 1 are 1 ≤ t, t + 2 ≤ d); reason: zero-based finite indexing; same instances and same sets
--   - generalization: Algorithm 3 with the lists L_1, …, L_{n+1} returned by Lemma 4.2 (procedure of Algorithm 2) and the answers of the ORS of Lemma 4.5 → Alg3Output: any profit-sorting order σ (ties), any lists satisfying Lemma 4.2's bullets 2–4 with error δ = ε²ρ/(2(d−1)) (RepFamily, without the size bullet), any correct answer to every range query (ties), any iteration order; reason: every run of the paper's algorithm is one of these runs; correctness does not use the size bound; a larger class of runs makes the claim stronger
--   - encoding: virtual items v in L_i, p(v), w̄(v), set(v), S₂ ∪ {v} → virtual items identified with their sets: v : Finset (Fin n), p(v) = p(set v), S₂ ∪ {v} is S₂ ∪ v; reason: the algorithm uses a virtual item only through p, w̄ and set
--   - encoding: p(S) ≥ (1 − ε)·OPT, OPT an optimal solution → IsApprox: S feasible and (1 − ε)·p(S') ≤ p(S) for every feasible S'; reason: OPT attains the maximum over the finitely many feasible sets; equivalent
--   - generalization: §2 assumes every item individually fits the capacities → all nonnegative instances, including individually infeasible items; reason: range queries reject every infeasible candidate; the proof uses only subsets of an optimal feasible solution, whose individual items fit
-- source:
--   Bringmann, Kulik, Węgrzycki (2026), Fine-Grained Complexity of Approximating Vector Knapsack: A Faster Algorithm and Equivalence with k-SUM in 2D, STOC 2027 submission, SHA-256 966f42f7…10ac98; Lemma 4.6, printed p. 19 (PDF 20); Algorithm 3, printed p. 19 (PDF 20)

import Mathlib
import Definitions.Def_VecKnapsackMitM_Main_Instance
import Definitions.Def_VecKnapsackMitM_Main_Algorithm3

namespace VecKnapsackMitM.Main

/-- Bringmann, Kulik, Węgrzycki (2026), Lemma 4.6, printed p. 19 (PDF 20). For every integer
`d ≥ 2`, `ρ ∈ (0, 1)` and `ε ∈ (0, (d − 1)/d]`, Algorithm 3 is a `(1 − ε)`-approximation
algorithm for d-Knapsack: on every instance, every set it can return (`Alg3Output`, over all
profit-sorting orders, all representative solutions with Lemma 4.2's guarantees for
`δ = ε²ρ/(2(d−1))`, all correct range-query answers and all iteration orders) is feasible with
profit at least `(1 − ε) · OPT`. -/
theorem lemma_4_6 (d n : ℕ) (hd : 2 ≤ d) (ρ ε : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hε0 : 0 < ε)
    (hε1 : ε ≤ ((d : ℝ) - 1) / d) (inst : Instance d n) (hinst : inst.Nonneg)
    (S : Finset (Fin n)) (hS : Alg3Output inst ε ρ S) : inst.IsApprox ε S := by sorry

end VecKnapsackMitM.Main
