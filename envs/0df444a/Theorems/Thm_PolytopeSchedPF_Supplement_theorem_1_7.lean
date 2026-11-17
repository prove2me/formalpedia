-- Prove2me | Theorems.Thm_PolytopeSchedPF_Supplement_theorem_1_7
-- name    : PolytopeSchedPF.Supplement.theorem_1_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:22:49.963492+00:00
-- url     : https://prove2.me/theorems/fa4352cb-d18c-4b10-9cc1-b427de53b7a7
-- title:
--   Theorem 1.7 — Proportional Fairness with speed $4+\varepsilon$ is $(4+\varepsilon)/\varepsilon$-competitive for weighted flow time in graph scheduling
-- statement:
--   Let $\varepsilon>0$, let $G$ be a loopless multigraph on a finite vertex set whose edges are the $n$ jobs, and let the rate polytope be its matching polytope $P_G$. For all weights $w\in\mathbb R^n_{>0}$, processing requirements $p\in\mathbb R^n_{\ge0}$ and release dates $r\in\mathbb R^n_{\ge0}$, the schedule of Proportional Fairness run with speed $4+\varepsilon$ and every feasible (speed-$1$) schedule $y'$ satisfy
--
--   $$\sum_jw_j\big(C^{\mathrm{pf}}_j-r_j\big)\le\frac{4+\varepsilon}{\varepsilon}\sum_jw_j\big(C_j(y')-r_j\big).$$
--
--   So PF is $(4+\varepsilon)$-speed $O(1/\varepsilon)$-competitive for weighted flow time in graph scheduling, the first such guarantee for a nonclairvoyant algorithm in this model.
--
--   Differences from the source:
--   - reading: O(1/ε)-competitive → the explicit factor (4 + ε)/ε for every ε > 0; reason: the constant the proof supplies: Corollary 6.12, factor κ/(κ − 2c) at c = 2, κ = 4 + ε; it is O(1/ε) for bounded ε
--   - encoding: PF with speed augmentation κ and its weighted flow time → a PF schedule for p/κ (rates in P), with flow time computed from completionTime (p/κ) r; reason: p.13: an s-speed feasible schedule for (p_j) is a 1-speed feasible schedule for (p_j/s), with the same completion times, and PF with speed s uses the same rule
--   - encoding: graph scheduling on a loopless multigraph G = (V, E) → any finite vertex type V, a loopless CombOpt.MatchingPolytope.Graph V (Fin n), and a RatePolytope P with P.rates = G.matchingPolytope; reason: the B-form of P_G exists by Edmonds' theorem (p.24) and is not assumed; parallel edges allowed
--   - encoding: ALG ≤ c · OPT, OPT the infimum over feasible schedules → ALG ≤ c · (objective of y′) for every feasible speed-1 schedule y′; reason: base reading R2: equivalent to the bound on the infimum
--   - encoding: the PF schedule → every schedule satisfying the base predicate IsPFSchedule; reason: base reading R4; existence of a PF schedule is the published PolytopeSchedPF.pf_schedule_exists
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, Theorem 1.7, p.4 (PDF p.6); proved through Corollary 6.12, p.39 (PDF p.41); graph scheduling §4.5, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_PolytopeSchedPF_ProportionalFairness
import Definitions.Def_PolytopeSchedPF_Supplement_weightedFlow
import Definitions.Def_CombOpt_MatchingPolytope_Graph_IsLoopless
import Definitions.Def_CombOpt_MatchingPolytope_Graph_matchingPolytope

namespace PolytopeSchedPF

namespace Supplement

/-- **Theorem 1.7** (Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1, p.4; proved through
Corollary 6.12, p.39). For every `ε > 0`, Proportional Fairness is `(4 + ε)`-speed
`O(1/ε)`-competitive for minimizing weighted flow time in graph scheduling.

For every `ε > 0`, every loopless multigraph `G` on a finite vertex set `V` with edge (job) set
`Fin n`, every rate polytope `P` whose rate set is the matching polytope `P_G`, weights `w > 0`,
processing requirements `p ≥ 0` and release dates `r ≥ 0`: every PF schedule with speed `4 + ε`
(a PF schedule for `p / (4 + ε)`) has weighted flow time at most `(4 + ε)/ε` times the weighted flow
time of every feasible speed-1 schedule for `p`.

**Formalization Note** `O(1/ε)` is stated with the constant the proof supplies: Corollary 6.12's
factor `κ/(κ − 2c)` at `c = 2`, `κ = 4 + ε`. Speed `κ` follows p.13: an `s`-speed feasible schedule
for `(p_j)` is a `1`-speed feasible schedule for `(p_j / s)`, and PF with speed `s` uses the same rule
(rates in `P`). Reading R2: the bound is against every feasible schedule. -/
theorem theorem_1_7 (ε : ℝ) (hε : 0 < ε) {V : Type*} [Fintype V] {n D : ℕ}
    (G : CombOpt.MatchingPolytope.Graph V (Fin n)) (hG : G.IsLoopless)
    (P : RatePolytope n D) (hPG : P.rates = G.matchingPolytope)
    (w p r : Fin n → ℝ) (hw : ∀ j, 0 < w j) (hp : ∀ j, 0 ≤ p j) (hr : ∀ j, 0 ≤ r j) :
    ∀ y, IsPFSchedule P w (fun j => p j / (4 + ε)) r y → ∀ y', IsFeasible P p r y' →
      weightedFlow w (fun j => p j / (4 + ε)) r y ≤ (4 + ε) / ε * weightedFlow w p r y' := by sorry

end Supplement

end PolytopeSchedPF
