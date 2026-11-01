-- Prove2me | Theorems.Thm_ParetoIneff_claim_5
-- name    : ParetoIneff.claim_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:29:23.915165+00:00
-- url     : https://prove2.me/theorems/278ae05d-9d94-4662-8a02-886ecab67346
-- title:
--   Claim 5 — at least $n-1$ tasks are well-behaved
-- statement:
--   Let $\alpha>1$ and let $\mathcal M$ be a mechanism on $n$ machines with equilibria at every profile and with $\mathrm{PoA}(\mathcal M)<(n-1)\alpha+1$. Let $m\ge\max\{2,2n-3\}$, let $\mathcal A_1,\dots,\mathcal A_m$ be anonymous components of the $m$-task part of $\mathcal M$, and fix a dummy list. Then there is a set of at least $n-1$ tasks, all of them well-behaved.
--
--   Otherwise $n-1$ tasks could all be sent to one slow machine in some equilibrium, which contradicts the bound on the Price of Anarchy.
--
--   Differences from the source:
--   - generalization: the proof fixes $m=\max\{2,2n-3\}$ tasks (p.13) → every $m\ge\max\{2,2n-3\}$; reason: the proof pads the instance with zero columns and works for any larger $m$; the printed $m$ is a special case
--   - reading: the class of Theorem 6 is named without its standing assumption → `Mech.HasEquilibria` is a hypothesis; reason: p.5: the paper considers only mechanisms with $\mathcal Q_t\ne\emptyset$ for every $t$
--   - reading: dummy machines have "arbitrarily high, pairwise distinct" processing times, written $\infty$ (p.13) → one fixed injective list $d$ of $n-2$ values above $((n-1)\alpha+1)\alpha$, shared by all canonical vectors (`IsDummyList`, `IsCanonical`); the statement holds for every such $d$; reason: canonical vectors are "permutations of $(1,\alpha,\infty,\dots,\infty)$" and the proof of Claim 4 uses that any two are permutations of each other; the threshold is the size the proof needs (the profile $\hat t$ of p.15 has optimum $\alpha$)
--   - reading: a mechanism on $n$ machines, with PoA and PoS a supremum over $m\in\mathbb N$ → a mechanism is a family indexed by the number of tasks $m$; reason: the supremum over $m$ only makes sense for such a family, and components may depend on $m$
--   - reading: the ratios of p.5 are not defined at $\mathrm{OPT}(t)=0$ → PoA and PoS are computed in $[0,\infty]$ with $c/0=\infty$ for $c\ne0$ and $0/0=0$; reason: the proof of Theorem 5 (p.11) treats positive$/0$ as unbounded, and an instance with zero optimum and zero makespan costs nothing
--   - encoding: allocations $x\in\{0,1\}^{n\times m}$ with $\sum_i x_{i,j}=1$, reports and costs in $\mathbb R_{\ge0}$, $\mathbb N=\{1,2,\dots\}$ → allocations are maps from tasks to machines, values are in `ℝ≥0`, machines and tasks are `Fin n`, `Fin m`, and $m=0$ is allowed; reason: the same instances; the case $m=0$ contributes $0/0=0$ to the suprema and only asks that the payments of an empty instance vanish, which changes no $m\ge1$ data
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, Claim 5, p.14; proof, p.15; m = max{2, 2n−3} from p.13

import Mathlib
import Definitions.Def_ParetoIneff_Mech_HasEquilibria
import Definitions.Def_ParetoIneff_Mech_PoA
import Definitions.Def_ParetoIneff_Mech_IsComponents
import Definitions.Def_ParetoIneff_SingleTaskMech_IsAnonymous
import Definitions.Def_ParetoIneff_IsDummyList
import Definitions.Def_ParetoIneff_IsWellBehaved

open NNReal

namespace ParetoIneff

/-- **Claim 5**, proof of Theorem 6, arXiv:1809.03454v7, p.14: mechanism `ℳ` has at least `n − 1`
well-behaved tasks.

Let `α > 1` and let `ℳ` be a mechanism on `n` machines with equilibria at every profile and
`PoA(ℳ) < (n − 1)α + 1`. Let `m ≥ max{2, 2n − 3}`, let `𝒜_1, …, 𝒜_m` be anonymous components of the
`m`-task part of `ℳ`, and let `d` be a list of pairwise distinct dummy processing times above
`((n − 1)α + 1)α`. Then there is a set of at least `n − 1` tasks, each of which is well-behaved
(Definition 5).

**Formalization Note** The proof of Theorem 6 fixes `m = max{2, 2n − 3}` (p.13); the claim is
stated for every `m ≥ max{2, 2n − 3}`. `n − 1` and `2n − 3` are natural-number subtractions; for
`n ≥ 2`, where canonical vectors exist, they are exact, and for `n ≤ 1` the claim is trivial. -/
theorem claim_5 {n : ℕ} (α : ℝ) (hα : 1 < α) (M : Mech n) (hM : M.HasEquilibria)
    (hPoA : M.PoA < ENNReal.ofReal (((n : ℝ) - 1) * α + 1))
    (m : ℕ) (hm : max 2 (2 * n - 3) ≤ m) (A : Fin m → SingleTaskMech n)
    (hA : M.IsComponents m A) (hanon : ∀ j : Fin m, (A j).IsAnonymous)
    (d : Fin (n - 2) → ℝ≥0) (hd : IsDummyList α d) :
    ∃ S : Finset (Fin m), n - 1 ≤ S.card ∧ ∀ j ∈ S, IsWellBehaved α d (A j) := by sorry

end ParetoIneff
