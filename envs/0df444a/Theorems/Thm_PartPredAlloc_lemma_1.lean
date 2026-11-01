-- Prove2me | Theorems.Thm_PartPredAlloc_lemma_1
-- name    : PartPredAlloc.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:19:11.163579+00:00
-- url     : https://prove2.me/theorems/c4284c12-3dce-4145-929b-6f92658b5c3f
-- title:
--   Lemma 1, p.12 — the event $\mathcal E$ has probability at least $1-\epsilon$
-- statement:
--   Let $\alpha=10+2\sqrt6$, $\bar\epsilon=1/24$ and $k=16$, and let $n\ge3$, $p\in(0,1)$ and $\vec v_I$ be arbitrary. For any $\epsilon\in[\frac1n,\bar\epsilon]$, with probability at least $1-\epsilon$ all of the following hold:
--
--   1. if $n_1\ge\frac k{p^2}\log n$, then for all $\lambda\in\{0,1/n,\dots,1\}$,
--   $$
--   |O_1(\lambda)-\tilde o_1(\lambda)|<\alpha\sqrt{n_1\log n}\quad\text{and}\quad|O_1(\lambda)+O_2(\lambda)-(\tilde o_1(\lambda)+\tilde o_2(\lambda))|<\alpha\sqrt{(n_1+n_2)\log n};
--   $$
--   2. if $n_2\ge\frac k{p^2}\log n$, then for all $\lambda\in\{0,1/n,\dots,1\}$,
--   $$
--   |O_2(\lambda)-\tilde o_2(\lambda)|<\alpha\sqrt{n_2\log n}\quad\text{and}\quad|O^{\mathcal S}_2(\lambda)-\tilde o^{\mathcal S}_2(\lambda)|<\alpha\sqrt{n_2\log n}.
--   $$
--
--   Equivalently, $\Pr(\mathcal E)\ge1-\epsilon$. This lets the algorithm estimate future demand from past observations; for $n<24$ the range of $\epsilon$ is empty and the statement holds vacuously, as printed.
--
--   Differences from the source:
--   - encoding: "with probability at least 1 − ε, all the following statements hold" (2a)–(3b) → 1 − ε ≤ prob n p (EventE p vI); reason: EventE is Definition 4, which collects exactly (2a)–(3b)
--   - encoding: probability over the stochastic group S and the random permutation σ_S → prob n p: explicit finite sum with weights p^{|S|}(1−p)^{n−|S|} and σ uniform over the permutations fixing every position outside S; reason: the model has finitely many outcomes; this is its law (§3, p.10), with no measure theory
-- source:
--   Hwang, Jaillet, Manshadi, Online Resource Allocation under Partially Predictable Demand, arXiv:1810.00447v1, Lemma 1, p.12; Definition 4, pp.13–14

import Mathlib
import Definitions.Def_PartPredAlloc_EventE

namespace PartPredAlloc

/-- **Lemma 1** (Hwang–Jaillet–Manshadi, arXiv:1810.00447v1, Lemma 1, p.12). Let `α = 10 + 2√6`,
`ε̄ = 1/24` and `k = 16`. For any `ε ∈ [1/n, ε̄]`, with probability at least `1 − ε` all the
statements (2a)–(3b) hold, i.e. the event `𝓔` of Definition 4 occurs.

**Formalization Note.** The probability is over the outcome `(S, σ)` of the partially predictable
model; `EventE` collects (2a)–(3b) for all `λ ∈ {0, 1/n, …, 1}`. Standing assumptions: `n ≥ 3`,
`p ∈ (0, 1)`. For `n < 24` the range `[1/n, 1/24]` is empty and the statement is vacuous, as
printed. -/
theorem lemma_1 {n : ℕ} (hn : 3 ≤ n) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (vI : Fin n → Cust) (ε : ℝ) (hε0 : 1 / (n : ℝ) ≤ ε) (hε : ε ≤ epsBar) :
    1 - ε ≤ prob n p (fun S σ => EventE p vI S σ) := by sorry

end PartPredAlloc
