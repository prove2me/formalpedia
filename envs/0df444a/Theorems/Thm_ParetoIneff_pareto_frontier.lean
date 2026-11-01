-- Prove2me | Theorems.Thm_ParetoIneff_pareto_frontier
-- name    : ParetoIneff.pareto_frontier
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:30:23.609286+00:00
-- url     : https://prove2.me/theorems/08a8ba32-dc3d-4cd2-8044-1544082f9168
-- title:
--   Theorems 6, 7, 8 — the PoA/PoS Pareto frontier of anonymous task-independent scheduling is attained exactly by $\mathcal{SP}_\alpha$ (corrected: attainment for $\alpha>1$)
-- statement:
--   Let $n\ge1$ be the number of machines.
--
--   1. **Lower boundary (Theorem 6).** For every real $\alpha>1$ and every task-independent anonymous mechanism $\mathcal M$ with equilibria at every profile,
--   $$
--   \mathrm{PoA}(\mathcal M)<(n-1)\alpha+1\ \Longrightarrow\ \mathrm{PoS}(\mathcal M)\ge\frac{n-1}{\alpha}+1.
--   $$
--   2. **Attainment (Theorems 7 and 8).** If $n\ge2$, then for every real $\alpha>1$ and every tie-breaking rule, the second-price mechanism with $\alpha$-relative reserve price $\mathcal{SP}_\alpha$ is task-independent and anonymous, has an equilibrium at every profile, and
--   $$
--   \mathrm{PoA}(\mathcal{SP}_\alpha)=(n-1)\alpha+1,\qquad \mathrm{PoS}(\mathcal{SP}_\alpha)=\frac{n-1}{\alpha}+1.
--   $$
--
--   Together these describe the Pareto frontier $(x-1)(y-1)=(n-1)^2$ between the two notions of inefficiency for this class: no mechanism in the class lies strictly below the curve, and each point of it is achieved.
--
--   **Formalization Note** At $n=1$ the hypothesis of clause 1 cannot hold, so clause 1 carries content from $n=2$ on, where clause 2 at a smaller $\alpha$ exhibits members of the class that satisfy it.
--
--   Differences from the source:
--   - generalization: Theorems 7 and 8 print $\le$ → equalities for $\mathrm{PoA}(\mathcal{SP}_\alpha)$ and $\mathrm{PoS}(\mathcal{SP}_\alpha)$; reason: they follow from clause 1 and the printed upper bounds by perturbing $\alpha$, and they are the abstract's "lie exactly on this frontier"; the printed bounds are implied
--   - correction: Definition 6 allows $\alpha\ge1$, and Theorems 7 and 8 state no range → clause 2 quantifies over $\alpha>1$; reason: counterexample: $\alpha=1$, $n=2$, ties to machine 2, $t=(1,2)$ has no equilibrium, so $\mathcal{SP}_1$ leaves the class and $\mathrm{PoS}=\infty$; both printed proofs fix $\alpha>1$, as does Theorem 6
--   - reading: Definition 6 and the statements about $\mathcal{SP}_\alpha$ name no range of $n$ → $n\ge2$; reason: at $n=1$ the second-lowest report is a minimum over the empty set and the payment is undefined
--   - reading: the class of Theorem 6 is named without its standing assumption → `Mech.HasEquilibria` is a hypothesis; reason: p.5: the paper considers only mechanisms with $\mathcal Q_t\ne\emptyset$ for every $t$
--   - reading: a mechanism on $n$ machines, with PoA and PoS a supremum over $m\in\mathbb N$ → a mechanism is a family indexed by the number of tasks $m$; reason: the supremum over $m$ only makes sense for such a family, and components may depend on $m$
--   - reading: the ratios of p.5 are not defined at $\mathrm{OPT}(t)=0$ → PoA and PoS are computed in $[0,\infty]$ with $c/0=\infty$ for $c\ne0$ and $0/0=0$; reason: the proof of Theorem 5 (p.11) treats positive$/0$ as unbounded, and an instance with zero optimum and zero makespan costs nothing
--   - encoding: allocations $x\in\{0,1\}^{n\times m}$ with $\sum_i x_{i,j}=1$, reports and costs in $\mathbb R_{\ge0}$, $\mathbb N=\{1,2,\dots\}$ → allocations are maps from tasks to machines, values are in `ℝ≥0`, machines and tasks are `Fin n`, `Fin m`, and $m=0$ is allowed; reason: the same instances; the case $m=0$ contributes $0/0=0$ to the suprema and only asks that the payments of an empty instance vanish, which changes no $m\ge1$ data
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, Theorem 6, p.13; Theorem 7, p.17; Theorem 8, p.18; abstract, p.1; §1.1, p.2; §4, p.12

import Mathlib
import Definitions.Def_ParetoIneff_Mech_HasEquilibria
import Definitions.Def_ParetoIneff_Mech_PoA
import Definitions.Def_ParetoIneff_Mech_PoS
import Definitions.Def_ParetoIneff_Mech_TaskIndepAnon
import Definitions.Def_ParetoIneff_SP

open NNReal

namespace ParetoIneff

/-- **The PoA/PoS Pareto frontier of anonymous task-independent scheduling**, Theorems 6, 7 and 8,
Filos-Ratsikas, Giannakopoulos, Lazos, *The Pareto frontier of inefficiency in mechanism design*,
arXiv:1809.03454v7, pp.13, 17, 18 (abstract, p.1: "we completely characterize the PoA/PoS Pareto
frontier; we design a class of optimal mechanisms `𝒮𝒫_α` that lie exactly on this frontier").

For `n ≥ 1` machines:

1. (Theorem 6, the lower boundary) for every real `α > 1` and every task-independent anonymous
   mechanism `ℳ` with equilibria at every profile,
   `PoA(ℳ) < (n − 1)α + 1 ⟹ PoS(ℳ) ≥ (n − 1)/α + 1`;
2. (Theorems 7 and 8, attainment) if `n ≥ 2`, then for every real `α > 1` and every tie-breaking
   rule `τ`, the second-price mechanism with `α`-relative reserve `𝒮𝒫_α` is task-independent and
   anonymous, has an equilibrium at every profile, and
   `PoA(𝒮𝒫_α) = (n − 1)α + 1` and `PoS(𝒮𝒫_α) = (n − 1)/α + 1`.

**Formalization Note** Theorems 7 and 8 print `≤`; equality follows from clause 1 together with the
upper bounds (perturb `α`), and is what "lie exactly on this frontier" asserts. PoA and PoS are
`ℝ≥0∞`-valued suprema over all task counts and all true profiles in `ℝ≥0^{n×m}`, with `c/0 = ⊤` for
`c ≠ 0` and `0/0 = 0`. `(n : ℝ) − 1` is a real subtraction. -/
theorem pareto_frontier {n : ℕ} [NeZero n] :
    (∀ α : ℝ, 1 < α → ∀ M : Mech n, M.TaskIndepAnon → M.HasEquilibria →
      M.PoA < ENNReal.ofReal (((n : ℝ) - 1) * α + 1) →
        ENNReal.ofReal (((n : ℝ) - 1) / α + 1) ≤ M.PoS) ∧
    (2 ≤ n → ∀ α : ℝ, 1 < α → ∀ τ : TieRule n,
      (SP α τ).TaskIndepAnon ∧ (SP α τ).HasEquilibria ∧
        (SP α τ).PoA = ENNReal.ofReal (((n : ℝ) - 1) * α + 1) ∧
        (SP α τ).PoS = ENNReal.ofReal (((n : ℝ) - 1) / α + 1)) := by sorry

end ParetoIneff
