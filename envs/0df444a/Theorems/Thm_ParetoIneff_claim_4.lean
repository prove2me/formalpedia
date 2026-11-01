-- Prove2me | Theorems.Thm_ParetoIneff_claim_4
-- name    : ParetoIneff.claim_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:29:30.22215+00:00
-- url     : https://prove2.me/theorems/d116cadb-3f0e-4ed0-9ef1-56cb64efefa3
-- title:
--   Claim 4 — one canonical vector with all equilibria fast makes a task well-behaved
-- statement:
--   Let $\alpha>1$ and let $\mathcal M$ be a mechanism on $n$ machines with equilibria at every profile and with $\mathrm{PoA}(\mathcal M)<(n-1)\alpha+1$, with components $\mathcal A_1,\dots,\mathcal A_m$ of its $m$-task part, and fix a dummy list. If $\mathcal A_j$ is anonymous and there exists a true canonical cost vector with respect to which all equilibria of $\mathcal A_j$ assign the task to the fast machine, then task $j$ is well-behaved.
--
--   Anonymity is what spreads the property from one canonical vector to all of them.
--
--   Differences from the source:
--   - generalization: all components of $\mathcal M$ are anonymous → only the component $\mathcal A_j$ of the task in question is assumed anonymous; reason: the proof of Claim 4 applies Definition 2 to $\mathcal A_j$ alone; a mechanism in the paper's class satisfies the hypothesis
--   - reading: the class of Theorem 6 is named without its standing assumption → `Mech.HasEquilibria` is a hypothesis; reason: p.5: the paper considers only mechanisms with $\mathcal Q_t\ne\emptyset$ for every $t$
--   - reading: dummy machines have "arbitrarily high, pairwise distinct" processing times, written $\infty$ (p.13) → one fixed injective list $d$ of $n-2$ values above $((n-1)\alpha+1)\alpha$, shared by all canonical vectors (`IsDummyList`, `IsCanonical`); the statement holds for every such $d$; reason: canonical vectors are "permutations of $(1,\alpha,\infty,\dots,\infty)$" and the proof of Claim 4 uses that any two are permutations of each other; the threshold is the size the proof needs (the profile $\hat t$ of p.15 has optimum $\alpha$)
--   - reading: a mechanism on $n$ machines, with PoA and PoS a supremum over $m\in\mathbb N$ → a mechanism is a family indexed by the number of tasks $m$; reason: the supremum over $m$ only makes sense for such a family, and components may depend on $m$
--   - reading: the ratios of p.5 are not defined at $\mathrm{OPT}(t)=0$ → PoA and PoS are computed in $[0,\infty]$ with $c/0=\infty$ for $c\ne0$ and $0/0=0$; reason: the proof of Theorem 5 (p.11) treats positive$/0$ as unbounded, and an instance with zero optimum and zero makespan costs nothing
--   - encoding: allocations $x\in\{0,1\}^{n\times m}$ with $\sum_i x_{i,j}=1$, reports and costs in $\mathbb R_{\ge0}$, $\mathbb N=\{1,2,\dots\}$ → allocations are maps from tasks to machines, values are in `ℝ≥0`, machines and tasks are `Fin n`, `Fin m`, and $m=0$ is allowed; reason: the same instances; the case $m=0$ contributes $0/0=0$ to the suprema and only asks that the payments of an empty instance vanish, which changes no $m\ge1$ data
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, Claim 4, p.14

import Mathlib
import Definitions.Def_ParetoIneff_Mech_HasEquilibria
import Definitions.Def_ParetoIneff_Mech_PoA
import Definitions.Def_ParetoIneff_Mech_IsComponents
import Definitions.Def_ParetoIneff_SingleTaskMech_IsAnonymous
import Definitions.Def_ParetoIneff_IsDummyList
import Definitions.Def_ParetoIneff_IsCanonical
import Definitions.Def_ParetoIneff_IsWellBehaved

open NNReal

namespace ParetoIneff

/-- **Claim 4**, proof of Theorem 6, arXiv:1809.03454v7, p.14: a task is well-behaved if there
exists a true canonical cost vector with respect to which all equilibria assign it to the fast
machine.

Let `α > 1` and let `ℳ` be a mechanism on `n` machines with equilibria at every profile and
`PoA(ℳ) < (n − 1)α + 1`, with components `𝒜_1, …, 𝒜_m` of its `m`-task part, and let `d` be a list
of pairwise distinct dummy processing times above `((n − 1)α + 1)α`. If the component `𝒜_j` is
anonymous and some canonical vector has all equilibria of `𝒜_j` on its fast machine, then task `j`
is well-behaved (Definition 5): at every canonical vector, every equilibrium of `𝒜_j` assigns the
task to the fast machine.

**Formalization Note** Only the anonymity of the component `𝒜_j` itself is assumed (the paper's
mechanism has all components anonymous). -/
theorem claim_4 {n : ℕ} (α : ℝ) (hα : 1 < α) (M : Mech n) (hM : M.HasEquilibria)
    (hPoA : M.PoA < ENNReal.ofReal (((n : ℝ) - 1) * α + 1))
    (m : ℕ) (A : Fin m → SingleTaskMech n) (hA : M.IsComponents m A)
    (d : Fin (n - 2) → ℝ≥0) (hd : IsDummyList α d) (j : Fin m) (hanon : (A j).IsAnonymous)
    (h : ∃ (v : Fin n → ℝ≥0) (fast slow : Fin n), IsCanonical α d v fast slow ∧
      ∀ s : Fin n → ℝ≥0, (A j).IsEq v s → (A j).alloc s = fast) :
    IsWellBehaved α d (A j) := by sorry

end ParetoIneff
