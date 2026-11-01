-- Prove2me | Theorems.Thm_ParetoIneff_theorem_7
-- name    : ParetoIneff.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:29:25.29452+00:00
-- url     : https://prove2.me/theorems/3dd343af-253b-40f8-a231-5844ad1ff2d9
-- title:
--   Theorem 7 — the Price of Anarchy of $\mathcal{SP}_\alpha$ is at most $(n-1)\alpha+1$
-- statement:
--   Let $n\ge2$ and $\alpha\ge1$, and let ties be broken by any rule. The Price of Anarchy of $\mathcal{SP}_\alpha$ on $n$ machines satisfies
--   $$
--   \mathrm{PoA}(\mathcal{SP}_\alpha)\le(n-1)\alpha+1.
--   $$
--   So the reserve price bounds the damage of every equilibrium, in contrast with the plain Second-Price mechanism, whose Price of Anarchy is unbounded.
--
--   Differences from the source:
--   - reading: Definition 6 and the statements about $\mathcal{SP}_\alpha$ name no range of $n$ → $n\ge2$; reason: at $n=1$ the second-lowest report is a minimum over the empty set and the payment is undefined
--   - reading: the ratios of p.5 are not defined at $\mathrm{OPT}(t)=0$ → PoA and PoS are computed in $[0,\infty]$ with $c/0=\infty$ for $c\ne0$ and $0/0=0$; reason: the proof of Theorem 5 (p.11) treats positive$/0$ as unbounded, and an instance with zero optimum and zero makespan costs nothing
--   - encoding: allocations $x\in\{0,1\}^{n\times m}$ with $\sum_i x_{i,j}=1$, reports and costs in $\mathbb R_{\ge0}$, $\mathbb N=\{1,2,\dots\}$ → allocations are maps from tasks to machines, values are in `ℝ≥0`, machines and tasks are `Fin n`, `Fin m`, and $m=0$ is allowed; reason: the same instances; the case $m=0$ contributes $0/0=0$ to the suprema and only asks that the payments of an empty instance vanish, which changes no $m\ge1$ data
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, Theorem 7, p.17; proof, pp.17–18

import Mathlib
import Definitions.Def_ParetoIneff_Mech_PoA
import Definitions.Def_ParetoIneff_SP

open NNReal

namespace ParetoIneff

/-- **Theorem 7**, arXiv:1809.03454v7, p.17: the Price of Anarchy of `𝒮𝒫_α` on `n` machines is at
most `(n − 1)α + 1`.

For `n ≥ 2`, every `α ≥ 1` and every tie-breaking rule `τ`,
`PoA(𝒮𝒫_α) ≤ (n − 1)α + 1`.

**Formalization Note** `α ≥ 1` is the range of Definition 6. PoA is the `ℝ≥0∞`-valued supremum
over all task counts and all true profiles in `ℝ≥0^{n×m}`, with `c/0 = ⊤` for `c ≠ 0` and
`0/0 = 0`. `𝒮𝒫_α` needs `n ≥ 2` (its payment uses the second-lowest report). -/
theorem theorem_7 {n : ℕ} (hn : 2 ≤ n) (α : ℝ) (hα : 1 ≤ α) (τ : TieRule n) :
    (SP α τ).PoA ≤ ENNReal.ofReal (((n : ℝ) - 1) * α + 1) := by sorry

end ParetoIneff
