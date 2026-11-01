-- Prove2me | Theorems.Thm_ParetoIneff_sp_in_class
-- name    : ParetoIneff.sp_in_class
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:29:37.953076+00:00
-- url     : https://prove2.me/theorems/be846b01-d7eb-4f2a-814a-98964deaa6ab
-- title:
--   §4.2, p.16 — $\mathcal{SP}_\alpha$ is task-independent and anonymous and has equilibria at every profile
-- statement:
--   Let $n\ge2$, $\alpha>1$, and let ties be broken by any rule. Then $\mathcal{SP}_\alpha$ is task-independent, with anonymous components, and it has a pure Nash equilibrium at every true profile.
--
--   So the mechanisms $\mathcal{SP}_\alpha$ belong to the class of Theorem 6, as §4.2 presupposes when it says that they populate the boundary.
--
--   **Formalization Note** At $\alpha=1$ existence depends on the tie rule, which is why $\alpha>1$ is assumed.
--
--   Differences from the source:
--   - reading: Definition 6 and the statements about $\mathcal{SP}_\alpha$ name no range of $n$ → $n\ge2$; reason: at $n=1$ the second-lowest report is a minimum over the empty set and the payment is undefined
--   - reading: §4.2 says the mechanisms lie on the frontier of the class; no numbered statement places them in it → a stated theorem that $\mathcal{SP}_\alpha$ is in the class; reason: the frontier claim presupposes it, and the existence half is not stated anywhere on the page
--   - encoding: allocations $x\in\{0,1\}^{n\times m}$ with $\sum_i x_{i,j}=1$, reports and costs in $\mathbb R_{\ge0}$, $\mathbb N=\{1,2,\dots\}$ → allocations are maps from tasks to machines, values are in `ℝ≥0`, machines and tasks are `Fin n`, `Fin m`, and $m=0$ is allowed; reason: the same instances; the case $m=0$ contributes $0/0=0$ to the suprema and only asks that the payments of an empty instance vanish, which changes no $m\ge1$ data
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, §4.2, p.16 (unnumbered); Definitions 1, 2, 6, p.6, p.16; p.5 standing assumption

import Mathlib
import Definitions.Def_ParetoIneff_Mech_HasEquilibria
import Definitions.Def_ParetoIneff_Mech_TaskIndepAnon
import Definitions.Def_ParetoIneff_SP

open NNReal

namespace ParetoIneff

/-- **`𝒮𝒫_α` is in the class of Theorem 6**, §4.2, arXiv:1809.03454v7, p.16 ("these mechanisms
achieve trade-offs that lie on the Pareto frontier of inefficiency for the class of
task-independent and anonymous mechanisms"): for `n ≥ 2`, every `α > 1` and every tie-breaking rule
`τ`, the mechanism `𝒮𝒫_α` is task-independent with anonymous components (Definitions 1–2) and has a
pure Nash equilibrium at every true profile (the standing assumption of p.5).

**Formalization Note** At `α = 1` equilibrium existence depends on the tie-breaking rule (see
`ParetoIneff.theorem_8`), which is why `α > 1` is assumed here. -/
theorem sp_in_class {n : ℕ} (hn : 2 ≤ n) (α : ℝ) (hα : 1 < α) (τ : TieRule n) :
    (SP α τ).TaskIndepAnon ∧ (SP α τ).HasEquilibria := by sorry

end ParetoIneff
