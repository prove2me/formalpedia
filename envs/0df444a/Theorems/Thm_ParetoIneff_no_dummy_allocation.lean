-- Prove2me | Theorems.Thm_ParetoIneff_no_dummy_allocation
-- name    : ParetoIneff.no_dummy_allocation
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:29:40.470277+00:00
-- url     : https://prove2.me/theorems/3644def1-27b3-410b-a3f9-43003bf85c7c
-- title:
--   Proof of Theorem 6, p.13 — no equilibrium allocates a task to a dummy machine
-- statement:
--   Let $\alpha>1$ and let $\mathcal M$ be a mechanism on $n$ machines with equilibria at every profile and with
--   $$
--   \mathrm{PoA}(\mathcal M)<(n-1)\alpha+1.
--   $$
--   Let $\mathcal A_1,\dots,\mathcal A_m$ be components of its $m$-task part and fix a dummy list. Then for every task $j$ and every true canonical cost vector $v$ with fast machine $i'$ and slow machine $i''$, every equilibrium of $\mathcal A_j$ under $v$ allocates the task to $i'$ or to $i''$.
--
--   So no component can put a task on a dummy machine.
--
--   Differences from the source:
--   - reading: "since $\mathcal M$ has a bounded PoA" → $\mathrm{PoA}(\mathcal M)<(n-1)\alpha+1$, with dummy values above $((n-1)\alpha+1)\alpha$; reason: p.13 fixes this assumption on PoA just before, and the dummy values are chosen high relative to it
--   - reading: the class of Theorem 6 is named without its standing assumption → `Mech.HasEquilibria` is a hypothesis; reason: p.5: the paper considers only mechanisms with $\mathcal Q_t\ne\emptyset$ for every $t$
--   - generalization: $\mathcal M$ is a mechanism of the class of Theorem 6 (task-independent and anonymous) → only that $\mathcal A_1,\dots,\mathcal A_m$ are components of the $m$-task part of $\mathcal M$; anonymity is not assumed; reason: the argument uses only task independence (footnote 10) and the PoA bound; every mechanism of the paper's class satisfies the hypotheses
--   - reading: dummy machines have "arbitrarily high, pairwise distinct" processing times, written $\infty$ (p.13) → one fixed injective list $d$ of $n-2$ values above $((n-1)\alpha+1)\alpha$, shared by all canonical vectors (`IsDummyList`, `IsCanonical`); the statement holds for every such $d$; reason: canonical vectors are "permutations of $(1,\alpha,\infty,\dots,\infty)$" and the proof of Claim 4 uses that any two are permutations of each other; the threshold is the size the proof needs (the profile $\hat t$ of p.15 has optimum $\alpha$)
--   - reading: a mechanism on $n$ machines, with PoA and PoS a supremum over $m\in\mathbb N$ → a mechanism is a family indexed by the number of tasks $m$; reason: the supremum over $m$ only makes sense for such a family, and components may depend on $m$
--   - reading: the ratios of p.5 are not defined at $\mathrm{OPT}(t)=0$ → PoA and PoS are computed in $[0,\infty]$ with $c/0=\infty$ for $c\ne0$ and $0/0=0$; reason: the proof of Theorem 5 (p.11) treats positive$/0$ as unbounded, and an instance with zero optimum and zero makespan costs nothing
--   - encoding: allocations $x\in\{0,1\}^{n\times m}$ with $\sum_i x_{i,j}=1$, reports and costs in $\mathbb R_{\ge0}$, $\mathbb N=\{1,2,\dots\}$ → allocations are maps from tasks to machines, values are in `ℝ≥0`, machines and tasks are `Fin n`, `Fin m`, and $m=0$ is allowed; reason: the same instances; the case $m=0$ contributes $0/0=0$ to the suprema and only asks that the payments of an empty instance vanish, which changes no $m\ge1$ data
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, proof of Theorem 6, p.13, "Notice that, since M has a bounded PoA"

import Mathlib
import Definitions.Def_ParetoIneff_Mech_HasEquilibria
import Definitions.Def_ParetoIneff_Mech_PoA
import Definitions.Def_ParetoIneff_Mech_IsComponents
import Definitions.Def_ParetoIneff_SingleTaskMech_IsEq
import Definitions.Def_ParetoIneff_IsDummyList
import Definitions.Def_ParetoIneff_IsCanonical

open NNReal

namespace ParetoIneff

/-- **No equilibrium on a dummy machine**, proof of Theorem 6, arXiv:1809.03454v7, p.13 ("Notice
that, since `ℳ` has a bounded PoA, none of its component mechanisms `𝒜_j` can have an equilibrium,
on any true canonical cost vector `tʲ`, that allocates task `j` to a dummy machine").

Let `α > 1` and let `ℳ` be a mechanism on `n` machines with equilibria at every profile and
`PoA(ℳ) < (n − 1)α + 1`. Let `𝒜_1, …, 𝒜_m` be components of its `m`-task part and `d` a list of
pairwise distinct dummy processing times above `((n − 1)α + 1)α`. Then every equilibrium of `𝒜_j`
under a canonical cost vector (fast machine `fast`, slow machine `slow`, dummy times `d`) allocates
the task to the fast or to the slow machine.

**Formalization Note** Anonymity of the components is not assumed: the argument uses only the
component property and the bounded PoA. Canonical vectors exist only for `n ≥ 2`. -/
theorem no_dummy_allocation {n : ℕ} (α : ℝ) (hα : 1 < α) (M : Mech n)
    (hM : M.HasEquilibria) (hPoA : M.PoA < ENNReal.ofReal (((n : ℝ) - 1) * α + 1))
    (m : ℕ) (A : Fin m → SingleTaskMech n) (hA : M.IsComponents m A)
    (d : Fin (n - 2) → ℝ≥0) (hd : IsDummyList α d)
    (j : Fin m) (v : Fin n → ℝ≥0) (fast slow : Fin n) (hv : IsCanonical α d v fast slow)
    (s : Fin n → ℝ≥0) (hs : (A j).IsEq v s) :
    (A j).alloc s = fast ∨ (A j).alloc s = slow := by sorry

end ParetoIneff
