-- Prove2me | Theorems.Thm_ParetoIneff_lemma_2
-- name    : ParetoIneff.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:28:07.06356+00:00
-- url     : https://prove2.me/theorems/24201580-a99b-488c-a0aa-1d5664219d5b
-- title:
--   Lemma 2 — "Nothing outside the bucket"
-- statement:
--   Let $n\ge2$, $\alpha\ge1$, let ties be broken by any rule, and let $t\in\mathbb R_{\ge0}^{n\times m}$ be a true profile. In any equilibrium of $\mathcal{SP}_\alpha$ under $t$, any task $j$ can only be assigned to a machine with processing time at most
--   $$
--   \alpha\cdot\min_{i\in N}t_{i,j}.
--   $$
--   Together with Lemma 3 this identifies the *bucket* of each task: the machines that can receive it in equilibrium.
--
--   Differences from the source:
--   - reading: Definition 6 and the statements about $\mathcal{SP}_\alpha$ name no range of $n$ → $n\ge2$; reason: at $n=1$ the second-lowest report is a minimum over the empty set and the payment is undefined
--   - encoding: allocations $x\in\{0,1\}^{n\times m}$ with $\sum_i x_{i,j}=1$, reports and costs in $\mathbb R_{\ge0}$, $\mathbb N=\{1,2,\dots\}$ → allocations are maps from tasks to machines, values are in `ℝ≥0`, machines and tasks are `Fin n`, `Fin m`, and $m=0$ is allowed; reason: the same instances; the case $m=0$ contributes $0/0=0$ to the suprema and only asks that the payments of an empty instance vanish, which changes no $m\ge1$ data
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, Lemma 2, p.16; proof, pp.16–17

import Mathlib
import Definitions.Def_ParetoIneff_Mech_Q
import Definitions.Def_ParetoIneff_SP

open NNReal

namespace ParetoIneff

/-- **Lemma 2** ("Nothing outside the bucket"), arXiv:1809.03454v7, p.16: in any equilibrium of
`𝒮𝒫_α`, any task `j` can only be assigned to a machine with processing time at most
`α · min_{i∈N} t_{i,j}`.

For `n ≥ 2` machines, `α ≥ 1`, every tie-breaking rule `τ`, every number of tasks `m`, every true
profile `t ∈ ℝ≥0^{n×m}`, every equilibrium `s` of `𝒮𝒫_α` under `t` and every task `j`, the machine
`ι(j)` that receives task `j` has `t_{ι(j),j} ≤ α · min_i t_{i,j}`.

**Formalization Note** `α ≥ 1` is the range of Definition 6. The minimum is the infimum in `ℝ≥0`
over the nonempty finite set of machines, cast to `ℝ`. -/
theorem lemma_2 {n : ℕ} (hn : 2 ≤ n) (α : ℝ) (hα : 1 ≤ α) (τ : TieRule n) (m : ℕ)
    (t s : Fin n → Fin m → ℝ≥0) (hs : s ∈ (SP α τ).Q m t) (j : Fin m) :
    (t ((SP α τ).alloc m s j) j : ℝ) ≤ α * ((⨅ i, t i j : ℝ≥0) : ℝ) := by sorry

end ParetoIneff
