-- Prove2me | Theorems.Thm_RSListDecodingCapacity_AllRates_theorem_4_1
-- name    : RSListDecodingCapacity.AllRates.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:10:45.84697+00:00
-- url     : https://prove2.me/theorems/16592e36-b755-4b78-a0db-07e505104c4e
-- title:
--   Theorem 4.1 (Main Result) — Algorithm 1 list decodes rate $(1-\theta)\varepsilon$ up to radius $1-\varepsilon$
-- statement:
--   There is an absolute constant $c>0$ such that the following holds. Fix $\varepsilon,\theta\in(0,1)$ with
--   $$\varepsilon<\Big(\frac{\theta^3(1-\theta)}{768}\Big)^{\frac{5+\theta}{1-\theta}}. \tag{27}$$
--   There is a deterministic implementation of Algorithm 1 at these $\varepsilon,\theta$ such that for all $n\ge k\ge1$ with $k>\lceil\varepsilon^{-3/\theta}\rceil$ and $k/n\le(1-\theta)\varepsilon$, every prime $q\ge\max(n,\,4\varepsilon^{1-9/\theta}n/k)$, all distinct evaluation points $\alpha_1,\dots,\alpha_n\in\mathbb F_q$ and every received word $(y_1,\dots,y_n)\in\mathbb F_q^n$, it outputs, in at most $q^{c\,\varepsilon^{-12/\theta}}$ charged steps across its interpolation, root-finding and pruning stages, the list of all $P\in\mathbb F_q[X]$ of degree less than $k$ whose agreement with $y$ is at least $\varepsilon n$, each exactly once. Furthermore, this list has at most $q^{c\,\varepsilon^{-3/\theta}}$ entries.
--
--   This is the low-rate decoder; Corollary 5.1 reduces every constant rate to it by padding.
--
--   **Formalization Note** `Algorithm1RunsWithin` requires the actual interpolation, differential-equation root-finding and pruning stages of Algorithm 1. Each stage is a finite deterministic Turing program, and its actual binary input and output are linked to the next stage. The running time is the sum of all three step counts plus two stage transitions. No program is assumed correct or efficient: the theorem concludes its execution, intermediate specifications, exact final list and both bounds. The natural parameters determined solely by $\varepsilon,\theta$ may be compiled into the program, while $A=\lceil\varepsilon n\rceil$ is supplied in the input.
--
--   Differences from the source:
--   - reading: Algorithm 1 outputs, in q^O(ε^(−12/θ)) time, a list … → one finite three-stage implementation of Algorithm 1 for each ε, θ, with one absolute constant c before ε, θ; reason: steps 3 and 4 leave the linear-system and root-finding routines unspecified; the conclusion supplies fixed deterministic programs and verifies their intermediate outputs and total charged execution on every legal input
--   - encoding: input parameters n, k, q, θ, ε, α, y with real ε, θ → ε, θ fixed in the programs; input n, k, q, A = ⌈εn⌉, α, y in binary; reason: d, m, W and the bound defining 𝓑 are fixed natural parameters that may be compiled into the interpolation program; A is the varying threshold and integer agreement ≥ εn is equivalent to agreement ≥ A
--   - encoding: Algorithm 1, unspecified machine model and output format, q^O(ε^(−12/θ)) time → Algorithm1RunsWithin charges all three Turing executions plus two stage transitions, outputs length-k coefficient vectors, and retains the intermediate interpolant and complete root list in the execution relation; reason: each intermediate output is exactly the next input, including the original data; no copying, root finding or filtering has free cost; polynomial simulations with a single Turing machine preserve q^O(f), with overhead absorbed by the absolute c
-- source:
--   Joshua Brakensiek, Yeyuan Chen, Aaron Putterman, Zihan Zhang, Kai Zhe Zheng, Algorithmic List Decoding of Reed–Solomon Codes up to Capacity, STOC 2027 submission #565 (October 2026), p.26, Theorem 4.1 and Algorithm 1 (proof p.27)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RSListDecodingCapacity_AllRates_Decoding
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_RSListDecodingCapacity_AllRates_Parameters
import Definitions.Def_RSListDecodingCapacity_AllRates_Algorithm1

open Polynomial

namespace RSListDecodingCapacity.AllRates

/-- **Theorem 4.1 (Main Result)** (Brakensiek–Chen–Putterman–Zhang–Zheng, STOC 2027 submission #565,
p.26). There is an absolute constant `c > 0` such that for all `ε, θ ∈ (0, 1)` with (27) there is a
deterministic implementation `M` of Algorithm 1 at these `ε, θ` with: for
all `n ≥ k ≥ 1` with `k > ⌈ε^{−3/θ}⌉` and `k/n ≤ (1 − θ)ε`, every prime
`q ≥ max(n, 4 ε^{1−9/θ} n/k)`, all distinct `α₁, …, αₙ ∈ 𝔽_q` and every `y ∈ 𝔽_qⁿ`, started on
`n, k, q, A = ⌈εn⌉, α, y`, its interpolation, root-finding and pruning machines run within a total
of `q^{c ε^{−12/θ}}` steps and output the list of all `P ∈ 𝔽_q[X]`
of degree less than `k` with agreement at least `εn` with `y`, each once; the list has at most
`q^{c ε^{−3/θ}}` entries. -/
theorem theorem_4_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ ε θ : ℝ, 0 < ε → ε < 1 → 0 < θ → θ < 1 → Cond21 ε θ →
      ∃ M : Algorithm1Program,
        ∀ n k : ℕ, 1 ≤ k → k ≤ n → paramD ε θ < k → (k : ℝ) / n ≤ (1 - θ) * ε →
        ∀ q : ℕ, q.Prime → (n : ℝ) ≤ q → 4 * ε ^ (1 - 9 / θ) * n / k ≤ (q : ℝ) →
        ∀ α : Fin n → ZMod q, Function.Injective α → ∀ y : Fin n → ZMod q,
          ∃ L : List (ZMod q)[X], L.Nodup ∧
            (∀ P : (ZMod q)[X], P ∈ L ↔ P ∈ listDecodingSet k α y (ε * n)) ∧
            Algorithm1RunsWithin M ε θ k α y L ⌊(q : ℝ) ^ (c * ε ^ (-12 / θ))⌋₊ ∧
            (L.length : ℝ) ≤ (q : ℝ) ^ (c * ε ^ (-3 / θ)) := by sorry

end RSListDecodingCapacity.AllRates
