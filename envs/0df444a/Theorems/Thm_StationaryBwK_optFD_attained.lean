-- Prove2me | Theorems.Thm_StationaryBwK_optFD_attained
-- name    : StationaryBwK.optFD_attained
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:51:13.547366+00:00
-- url     : https://prove2.me/theorems/1de70ccb-0c8a-43cd-bc5e-790c6699da07
-- title:
--   Display (1): the optimum $(T^*,A^*)$ of $\mathrm{OPT}_{FD}$ is attained
-- statement:
--   Let $T\ge1$, $0<B\le T$, and let $r_t(a)$, $c_{t,i}(a)$ be real sequences such that a null action $a_0$ has $c_{t,i}(a_0)=0$ for every round $t\in[T]$ and resource $i$. Then problem (1),
--   $$\max_{T^*\in[T],\ A^*\in\Delta([K])}\sum_{t=1}^{T^*}\mathbb E_{a\sim A^*}[r_t(a)]\quad\text{s.t.}\quad\sum_{t=1}^{T^*}\mathbb E_{a\sim A^*}[c_{t,i}(a)]\le B\ \ \forall i,$$
--   has an optimal solution $(T^*,A^*)$, and its value equals $\mathrm{OPT}_{FD}$.
--
--   The paper refers to "the solution" $(T^*,A^*)$ of (1); Lemmas A.1, A.2 and the proof of Theorem 5.2 are built on it.
--
--   Differences from the source:
--   - generalization: r_t(a), c_{t,i}(a) the conditional expectations of one realized history, in [0, 1] → arbitrary real sequences r, c; reason: the proof uses only the stated hypotheses; the paper applies it at each outcome, where r, c are such sequences
--   - encoding: OPT_FD = max over T* ∈ [T], A* ∈ Δ([K]) in (1) → the supremum (sSup) of the feasible values, which is attained (optFD_attained); reason: Lean convention; equal to the maximum whenever it exists
--   - encoding: rounds t ∈ [T], actions [K] with a null action, resources [d], Alg_min's choice i ∈ [d] ∪ {0} → rounds are natural numbers 1, …, T; actions Fin K with a designated null action a₀; resources Fin d; i ∈ Option (Fin d) with none = 0; reason: Lean convention; same instances
-- source:
--   G. Fikioris and É. Tardos, Approximately Stationary Bandits with Knapsacks, arXiv:2302.14686v2 [cs.LG] (preprint, 8 Jul 2023), https://arxiv.org/abs/2302.14686v2, §4, p.7, display (1) and "We denote with (T∗, A∗) the solution to the above optimization problem"

import Mathlib
import Definitions.Def_StationaryBwK_Benchmark

namespace StationaryBwK

/-- **The optimum of (1) is attained** (Fikioris & Tardos, arXiv:2302.14686v2, §4, p.7: "We denote
with `(T∗, A∗)` the solution to the above optimization problem"). For a horizon `T ≥ 1`, a budget
`0 < B ≤ T`, a null action `a₀` with zero consumption in every round `t ∈ [T]`, and any reward and
consumption sequences `r`, `c`, there is an optimal solution `(T*, A*)` of (1), and its value is
`OPT_FD`.

**Formalization Note.** Deterministic: the paper applies it to the conditional expectations of one
realized history. `r` and `c` are arbitrary real sequences. -/
theorem optFD_attained {d K : ℕ} (T : ℕ) (B : ℝ) (hT : 1 ≤ T) (hB : 0 < B) (hBT : B ≤ T)
    (a₀ : Fin K) (r : ℕ → Fin K → ℝ) (c : ℕ → Fin d → Fin K → ℝ)
    (hc₀ : ∀ t ∈ Finset.Icc 1 T, ∀ i, c t i a₀ = 0) :
    ∃ (Ts : ℕ) (p : Fin K → ℝ), IsOptFDSolution T B r c Ts p ∧ fdValue r Ts p = optFD T B r c := by sorry

end StationaryBwK
