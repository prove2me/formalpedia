-- Prove2me | Theorems.Thm_ParetoIneff_lemma_3
-- name    : ParetoIneff.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:28:17.498679+00:00
-- url     : https://prove2.me/theorems/427bd7bb-b35e-4d1e-8c65-332019b3e5c0
-- title:
--   Lemma 3 — "Everything inside the bucket" (corrected: same-cost winner when the fastest cost is $0$ and tied)
-- statement:
--   Let $n\ge2$, $\alpha>1$, let ties be broken by any rule, and let $t\in\mathbb R_{\ge0}^{n\times m}$ be a true profile. For every choice of a machine $k_j$ in the bucket of each task $j$, that is
--   $$
--   t_{k_j,j}\le\alpha\cdot\min_{i\in N}t_{i,j},
--   $$
--   there is an equilibrium of $\mathcal{SP}_\alpha$ under $t$ in which, for every task $j$, the winner $\ell$ of task $j$ has the same cost, $t_{\ell,j}=t_{k_j,j}$, and $\ell=k_j$ whenever $\min_i t_{i,j}>0$ or $k_j$ is the only machine with cost $0$ for task $j$.
--
--   Same-cost winners leave all machine loads unchanged, which is what the proof of Theorem 8 uses.
--
--   Differences from the source:
--   - correction: every machine in the bucket can be allocated task $j$ → the winner has the same cost as the chosen machine, and is that machine unless the smallest cost is $0$ and attained twice; reason: counterexample: $n=2$, $t=(0,0)$, $\alpha=2$, ties to machine 1: if machine 2 wins with report $s_2>0$, machine 1 deviates to $s_2/2$ and gains; if $s_2=0$, machine 2 is paid $0$ and deviates to $s_1/2>0$, keeps the task and is paid more; the proof's Case 2 needs $t_f+\varepsilon<\alpha t_f$, impossible at $t_f=0$
--   - reading: "there exist equilibria of $\mathcal{SP}_\alpha$ such that for every task $j$, every machine ... can be allocated task $j$" → one equilibrium for each simultaneous choice of a bucket machine per task; reason: no single equilibrium serves all machines of a bucket; the proof of Theorem 8 (p.18) uses this form, and the per-task reading is the case in which only one task's choice matters
--   - reading: Definition 6 and the statements about $\mathcal{SP}_\alpha$ name no range of $n$ → $n\ge2$; reason: at $n=1$ the second-lowest report is a minimum over the empty set and the payment is undefined
--   - encoding: allocations $x\in\{0,1\}^{n\times m}$ with $\sum_i x_{i,j}=1$, reports and costs in $\mathbb R_{\ge0}$, $\mathbb N=\{1,2,\dots\}$ → allocations are maps from tasks to machines, values are in `ℝ≥0`, machines and tasks are `Fin n`, `Fin m`, and $m=0$ is allowed; reason: the same instances; the case $m=0$ contributes $0/0=0$ to the suprema and only asks that the payments of an empty instance vanish, which changes no $m\ge1$ data
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, Lemma 3, p.17; applied in the proof of Theorem 8, p.18

import Mathlib
import Definitions.Def_ParetoIneff_Mech_Q
import Definitions.Def_ParetoIneff_SP

open NNReal

namespace ParetoIneff

/-- **Lemma 3** ("Everything inside the bucket"), arXiv:1809.03454v7, p.17 (corrected: when the
fastest cost is `0` and tied, a same-cost winner):

For `n ≥ 2` machines, `α > 1`, every tie-breaking rule `τ`, every number of tasks `m`, every true
profile `t ∈ ℝ≥0^{n×m}` and every choice of a machine `k j` in the bucket of each task `j`
(`t_{k j, j} ≤ α · min_i t_{i,j}`), there is an equilibrium `s` of `𝒮𝒫_α` under `t` such that for
every task `j` the winner `ℓ` of task `j` has the same cost, `t_{ℓ,j} = t_{k j, j}`, and `ℓ = k j`
whenever `min_i t_{i,j} > 0` or `k j` is the only machine with `t_{i,j} = 0`.

**Formalization Note** The printed lemma says every machine in the bucket can be allocated the
task. That is false when the smallest cost is `0` and attained twice: for `n = 2`, `t = (0, 0)`,
`α = 2` and ties broken towards the first machine, no equilibrium gives the task to the second
machine. Away from that case the corrected statement is the printed one. The choice `k` is
simultaneous over the tasks, which is how the proof of Theorem 8 (p.18) applies the lemma; the
per-task reading is the special case in which only one `k j` matters. The minimum is the infimum in
`ℝ≥0` over the nonempty finite set of machines. -/
theorem lemma_3 {n : ℕ} (hn : 2 ≤ n) (α : ℝ) (hα : 1 < α) (τ : TieRule n) (m : ℕ)
    (t : Fin n → Fin m → ℝ≥0) (k : Fin m → Fin n)
    (hk : ∀ j, (t (k j) j : ℝ) ≤ α * ((⨅ i, t i j : ℝ≥0) : ℝ)) :
    ∃ s ∈ (SP α τ).Q m t, ∀ j, t ((SP α τ).alloc m s j) j = t (k j) j ∧
      ((0 < ⨅ i, t i j) ∨ (∀ i, t i j = 0 → i = k j) → (SP α τ).alloc m s j = k j) := by sorry

end ParetoIneff
