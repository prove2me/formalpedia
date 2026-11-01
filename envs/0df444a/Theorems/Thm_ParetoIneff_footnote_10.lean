-- Prove2me | Theorems.Thm_ParetoIneff_footnote_10
-- name    : ParetoIneff.footnote_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:26:51.062168+00:00
-- url     : https://prove2.me/theorems/7af49ee5-d537-481b-af1c-f3e74aa6af4e
-- title:
--   Footnote 10 — equilibria of a task-independent mechanism decompose by task
-- statement:
--   Let $\mathcal A_1,\dots,\mathcal A_m$ be components of the $m$-task part of a mechanism $\mathcal M$ (Definition 1). A profile of reports $s$ is an equilibrium of $\mathcal M$ with respect to a true profile $t$ if and only if, for every task $j$, the column $s^j$ is an equilibrium of $\mathcal A_j$ with respect to the column $t^j$.
--
--   Both directions are used throughout the paper, to assemble equilibria of a mechanism from those of its components and to read equilibria of the components from those of the mechanism.
--
--   Differences from the source:
--   - encoding: allocations $x\in\{0,1\}^{n\times m}$ with $\sum_i x_{i,j}=1$, reports and costs in $\mathbb R_{\ge0}$, $\mathbb N=\{1,2,\dots\}$ → allocations are maps from tasks to machines, values are in `ℝ≥0`, machines and tasks are `Fin n`, `Fin m`, and $m=0$ is allowed; reason: the same instances; the case $m=0$ contributes $0/0=0$ to the suprema and only asks that the payments of an empty instance vanish, which changes no $m\ge1$ data
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, footnote 10, p.13

import Mathlib
import Definitions.Def_ParetoIneff_Mech_IsEq
import Definitions.Def_ParetoIneff_Mech_IsComponents
import Definitions.Def_ParetoIneff_SingleTaskMech_IsEq

open NNReal

namespace ParetoIneff

/-- **Footnote 10**, proof of Theorem 6, Filos-Ratsikas, Giannakopoulos, Lazos, *The Pareto
frontier of inefficiency in mechanism design*, arXiv:1809.03454v7, p.13: if the single-task
mechanisms `𝒜_1, …, 𝒜_m` are components of the `m`-task part of `ℳ` (Definition 1), then a
reported profile `s` is an equilibrium of `ℳ` with respect to the true profile `t` if and only if,
for every task `j`, the column `sʲ` is an equilibrium of `𝒜_j` with respect to the column `tʲ`.

**Formalization Note** Only task-independence (the component property) is assumed, not
anonymity; footnote 10 calls the fact "an immediate consequence of task-independence". -/
theorem footnote_10 {n : ℕ} (M : Mech n) (m : ℕ) (A : Fin m → SingleTaskMech n)
    (hA : M.IsComponents m A) (t s : Fin n → Fin m → ℝ≥0) :
    M.IsEq m t s ↔ ∀ j : Fin m, (A j).IsEq (col t j) (col s j) := by sorry

end ParetoIneff
