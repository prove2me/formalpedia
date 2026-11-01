-- Prove2me | Theorems.Thm_ParetoIneff_theorem_8
-- name    : ParetoIneff.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:29:55.649988+00:00
-- url     : https://prove2.me/theorems/16f5d7b2-91cd-415f-bcd7-c6a0208103ce
-- title:
--   Theorem 8 — the Price of Stability of $\mathcal{SP}_\alpha$ is at most $(n-1)/\alpha+1$ (corrected: equilibrium existence assumed)
-- statement:
--   Let $n\ge2$ and $\alpha\ge1$, and let ties be broken by a rule under which $\mathcal{SP}_\alpha$ has an equilibrium at every profile. Then
--   $$
--   \mathrm{PoS}(\mathcal{SP}_\alpha)\le\frac{n-1}{\alpha}+1.
--   $$
--   For $\alpha>1$ the existence assumption holds for every rule. So this bound and Theorem 6 meet exactly.
--
--   Differences from the source:
--   - correction: Theorem 8 states no condition on the tie rule, and Definition 6 allows $\alpha=1$ with ties broken arbitrarily → `HasEquilibria` of $\mathcal{SP}_\alpha$ is a hypothesis; reason: counterexample: $\alpha=1$, $n=2$, ties to machine 2, $t=(1,2)$ has no equilibrium, so $\mathrm{PoS}=\infty$; the hypothesis is p.5's standing assumption, and it holds for every rule at $\alpha>1$ (`sp_in_class`)
--   - reading: Definition 6 and the statements about $\mathcal{SP}_\alpha$ name no range of $n$ → $n\ge2$; reason: at $n=1$ the second-lowest report is a minimum over the empty set and the payment is undefined
--   - reading: the ratios of p.5 are not defined at $\mathrm{OPT}(t)=0$ → PoA and PoS are computed in $[0,\infty]$ with $c/0=\infty$ for $c\ne0$ and $0/0=0$; reason: the proof of Theorem 5 (p.11) treats positive$/0$ as unbounded, and an instance with zero optimum and zero makespan costs nothing
--   - encoding: allocations $x\in\{0,1\}^{n\times m}$ with $\sum_i x_{i,j}=1$, reports and costs in $\mathbb R_{\ge0}$, $\mathbb N=\{1,2,\dots\}$ → allocations are maps from tasks to machines, values are in `ℝ≥0`, machines and tasks are `Fin n`, `Fin m`, and $m=0$ is allowed; reason: the same instances; the case $m=0$ contributes $0/0=0$ to the suprema and only asks that the payments of an empty instance vanish, which changes no $m\ge1$ data
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, Theorem 8, p.18; proof, pp.18–19

import Mathlib
import Definitions.Def_ParetoIneff_Mech_HasEquilibria
import Definitions.Def_ParetoIneff_Mech_PoS
import Definitions.Def_ParetoIneff_SP

open NNReal

namespace ParetoIneff

/-- **Theorem 8**, arXiv:1809.03454v7, p.18 (corrected: equilibrium existence assumed): the Price
of Stability of `𝒮𝒫_α` on `n` machines is at most `(n − 1)/α + 1`.

For `n ≥ 2`, every `α ≥ 1` and every tie-breaking rule `τ` for which `𝒮𝒫_α` has an equilibrium at
every profile, `PoS(𝒮𝒫_α) ≤ (n − 1)/α + 1`.

**Formalization Note** The existence hypothesis is the paper's standing assumption of p.5 made
explicit. It is needed at `α = 1`: with `n = 2`, ties broken towards the second machine and the
one-task profile `t = (1, 2)`, `𝒮𝒫_1` has no equilibrium, so `PoS = ⊤`. For `α > 1` it holds for
every tie-breaking rule (`ParetoIneff.sp_in_class`). PoS is the `ℝ≥0∞`-valued supremum over all
task counts and all true profiles in `ℝ≥0^{n×m}`. -/
theorem theorem_8 {n : ℕ} (hn : 2 ≤ n) (α : ℝ) (hα : 1 ≤ α) (τ : TieRule n)
    (hEq : (SP α τ).HasEquilibria) :
    (SP α τ).PoS ≤ ENNReal.ofReal (((n : ℝ) - 1) / α + 1) := by sorry

end ParetoIneff
