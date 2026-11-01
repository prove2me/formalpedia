-- Prove2me | Theorems.Thm_ParetoIneff_theorem_6
-- name    : ParetoIneff.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:29:55.344564+00:00
-- url     : https://prove2.me/theorems/cf7ba76b-36f6-4ad7-8ffa-5e2b6cbc16c6
-- title:
--   Theorem 6 — the inefficiency boundary for task-independent anonymous mechanisms
-- statement:
--   Let $\mathcal M$ be a task-independent anonymous scheduling mechanism for $n\ge1$ machines with equilibria at every profile, and let $\alpha>1$ be real. Then
--   $$
--   \mathrm{PoA}(\mathcal M)<(n-1)\alpha+1\ \Longrightarrow\ \mathrm{PoS}(\mathcal M)\ge\frac{n-1}{\alpha}+1.
--   $$
--   This is the lower boundary of the feasible PoA/PoS region: a mechanism in the class cannot improve its worst equilibrium below the bound without paying in its best equilibrium.
--
--   **Formalization Note** At $n=1$ the hypothesis says $\mathrm{PoA}(\mathcal M)<1$, which cannot hold, and the conclusion $\mathrm{PoS}(\mathcal M)\ge1$ is true anyway; the proof on p.13 takes $n\ge2$.
--
--   Differences from the source:
--   - reading: the class of Theorem 6 is named without its standing assumption → `Mech.HasEquilibria` is a hypothesis; reason: p.5: the paper considers only mechanisms with $\mathcal Q_t\ne\emptyset$ for every $t$
--   - reading: a mechanism on $n$ machines, with PoA and PoS a supremum over $m\in\mathbb N$ → a mechanism is a family indexed by the number of tasks $m$; reason: the supremum over $m$ only makes sense for such a family, and components may depend on $m$
--   - reading: the ratios of p.5 are not defined at $\mathrm{OPT}(t)=0$ → PoA and PoS are computed in $[0,\infty]$ with $c/0=\infty$ for $c\ne0$ and $0/0=0$; reason: the proof of Theorem 5 (p.11) treats positive$/0$ as unbounded, and an instance with zero optimum and zero makespan costs nothing
--   - encoding: allocations $x\in\{0,1\}^{n\times m}$ with $\sum_i x_{i,j}=1$, reports and costs in $\mathbb R_{\ge0}$, $\mathbb N=\{1,2,\dots\}$ → allocations are maps from tasks to machines, values are in `ℝ≥0`, machines and tasks are `Fin n`, `Fin m`, and $m=0$ is allowed; reason: the same instances; the case $m=0$ contributes $0/0=0$ to the suprema and only asks that the payments of an empty instance vanish, which changes no $m\ge1$ data
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, Theorem 6, p.13; proof, pp.13–16

import Mathlib
import Definitions.Def_ParetoIneff_Mech_HasEquilibria
import Definitions.Def_ParetoIneff_Mech_PoA
import Definitions.Def_ParetoIneff_Mech_PoS
import Definitions.Def_ParetoIneff_Mech_TaskIndepAnon

open NNReal

namespace ParetoIneff

/-- **Theorem 6**, Filos-Ratsikas, Giannakopoulos, Lazos, *The Pareto frontier of inefficiency in
mechanism design*, arXiv:1809.03454v7, p.13: for any task-independent anonymous scheduling
mechanism `ℳ` for `n` machines, and any real `α > 1`,
`PoA(ℳ) < (n − 1)α + 1 ⟹ PoS(ℳ) ≥ (n − 1)/α + 1`.

**Formalization Note** `ℳ` ranges over the paper's class: task-independent and anonymous
(`Mech.TaskIndepAnon`, Definitions 1–2) with equilibria at every profile (`Mech.HasEquilibria`,
the standing assumption of p.5). PoA and PoS are `ℝ≥0∞`-valued suprema over all task counts `m`
and all true profiles in `ℝ≥0^{n×m}`; the bounds are `ENNReal.ofReal` of real expressions, with
`(n : ℝ) − 1` a real subtraction. -/
theorem theorem_6 {n : ℕ} [NeZero n] (α : ℝ) (hα : 1 < α) (M : Mech n)
    (hTIA : M.TaskIndepAnon) (hM : M.HasEquilibria)
    (hPoA : M.PoA < ENNReal.ofReal (((n : ℝ) - 1) * α + 1)) :
    ENNReal.ofReal (((n : ℝ) - 1) / α + 1) ≤ M.PoS := by sorry

end ParetoIneff
