-- Prove2me | Theorems.Thm_PolytopeSchedPF_Supplement_theorem_1_5
-- name    : PolytopeSchedPF.Supplement.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:21:46.175147+00:00
-- url     : https://prove2.me/theorems/f2dfdffb-a0dc-4ff1-acdf-20ceb4631624
-- title:
--   Theorem 1.5 — every randomized nonclairvoyant algorithm for total completion time has competitive ratio at least $2+10^{-5}$, even in graph scheduling
-- statement:
--   Consider graph scheduling with unit weights and all release dates equal to $0$: the jobs are the edges of a loopless multigraph $G$ and the rate polytope is its matching polytope $P_G$. Let $c\in\mathbb R$, and suppose that on every such instance some randomized nonclairvoyant algorithm satisfies
--
--   $$\mathbb E\Big[\sum_{j}C_j\Big]\le c\cdot\mathrm{OPT}(p)\qquad\text{for every }p\in\mathbb R^n_{\ge0},$$
--
--   where the expectation is over the algorithm's internal randomness and $\mathrm{OPT}(p)$ is the optimal total completion time. Then
--
--   $$c\ge2+10^{-5}.$$
--
--   Hence no randomized nonclairvoyant algorithm is $2$-competitive on general polytope scheduling, whereas Proportional Fairness is $2$-competitive on every support-submodular polytope (Theorem 1.3). It is the first lower bound for polytope scheduling beyond the single-machine bound $2$.
--
--   Differences from the source:
--   - reading: the competitive ratio (the infimum of all c for which the algorithm is c-competitive, Definition 3.1) is at least 2 + 10⁻⁵ → every c for which c-competitive algorithms exist on all graph-scheduling instances satisfies 2 + 10⁻⁵ ≤ c; reason: a lower bound on an infimum is a lower bound on every element
--   - reading: randomized nonclairvoyant algorithm (informal model of §3.1 and the proof, p.40, p.43) → RandomizedPolicy: a probability space of any universe and, for every outcome, a deterministic policy feasible for every p ≥ 0 whose schedule on [0, t) is the same for inputs that differ only in jobs unfinished at t, with cost jointly measurable in (outcome, p); reason: the paper defines the model in prose; joint measurability is the standing convention behind the expectation E_{p,R} in its Yao step (p.43)
--   - encoding: one online algorithm for the class of graph-scheduling instances → for every instance P some randomized policy for P (which may depend on P, i.e. on B and n); reason: an online algorithm knows w_j and the column B_j of every job released at time 0; choosing one policy per instance is the same as one algorithm
--   - encoding: graph scheduling with uniform release dates; total completion time → RatePolytopes with P.rates = matching polytope of a loopless multigraph on vertex set Fin m, release dates 0, unit weights; OPT = base opt0 P 1 p; reason: the proof uses release dates 0; every finite vertex set is some Fin m up to relabeling
--   - encoding: expected cost ≤ c · OPT → lower Lebesgue integral of ofReal(∑_j C_j) ≤ ofReal(c · opt0 P 1 p) in ℝ≥0∞; reason: costs are nonnegative; a non-integrable cost counts as ∞ instead of 0
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, Theorem 1.5, p.3 (PDF p.5); restated and proved §7.1, pp.40–43 (PDF pp.42–45); Definition 3.1, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_PolytopeSchedPF_Supplement_Nonclairvoyant
import Definitions.Def_PolytopeSchedPF_Supplement_IsGraphScheduling

namespace PolytopeSchedPF

namespace Supplement

universe u

/-- **Theorem 1.5** (Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1, p.3; restated and proved
§7.1, pp.40–43). The competitive ratio of every randomized nonclairvoyant algorithm for total
completion time in PSP is at least `2 + 10⁻⁵`, even for graph scheduling with uniform release dates.

Let `c ∈ ℝ`. Suppose that on every graph-scheduling instance `P` (loopless multigraph, rate polytope
= matching polytope, any number of jobs) with unit weights and all release dates `0`, there is a
randomized nonclairvoyant algorithm whose expected total completion time is at most `c · OPT(p)` for
every `p ∈ ℝⁿ_{≥0}`. Then `c ≥ 2 + 10⁻⁵`.

**Formalization Note** "Competitive ratio at least `2 + 10⁻⁵`" (the infimum of the `c` for which the
algorithm is `c`-competitive, Definition 3.1) is stated as: every such `c` is at least `2 + 10⁻⁵`.
The algorithm may depend on the instance (`B` is known online once jobs are released, here at `0`),
so "one algorithm for the class" is "one randomized policy per instance". Uniform release dates are
release dates `0` (as in the proof). The random bits live in a type of an arbitrary universe `u`. -/
theorem theorem_1_5 (c : ℝ)
    (h : ∀ (n D : ℕ) (P : RatePolytope n D), IsGraphScheduling P →
      ∃ R : RandomizedPolicy.{u} P, R.IsCompetitive c) :
    2 + (1 / 10 : ℝ) ^ 5 ≤ c := by sorry

end Supplement

end PolytopeSchedPF
