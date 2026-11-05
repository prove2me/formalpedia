-- Prove2me | Theorems.Thm_VolunteerNotify_closing_step
-- name    : VolunteerNotify.closing_step
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:40:06.61759+00:00
-- url     : https://prove2.me/theorems/9d4cdbdd-d731-4375-8101-0c5de917efa0
-- title:
--   §4.2, p.21 — the SN policy completes at least $\frac1{2-q}f(x^*)$ tasks in expectation
-- statement:
--   Let $q$ be the MDHR of $g$, let $x^*$ be defined by (5), let $(\tilde x,J)$ solve (6)–(8) for the input $x^*$, and consider the online process with notification probabilities $\tilde x$. Then
--   $$
--   \mathrm{POL}_{\mathcal I}\ge\frac1{2-q}f(x^*).
--   $$
--   This is where the per-volunteer bounds are summed: the contributions under the priority scheme add up to the number of completed tasks.
--
--   Differences from the source:
--   - generalization: q is the minimum over τ ∈ ℕ of the hazard rates (Definition 1) → q is their infimum (`mdhr`); reason: the minimum need not exist, e.g. hazards 1/2 + 1/(τ+2); the infimum equals the minimum whenever it exists, so the statement specializes to the source
--   - generalization: x* is the argmax of f over the three candidates of (5) → `IsExAnte`: every value of (5) over any optimizer of (LP), any m ≥ 1 and Frank–Wolfe run, any solution of (SQ-v), and any tie-break; reason: the candidates are not unique; each run of the source is one such value
--   - reading: Algorithm 1: "Notify v with probability x̃_{v,s,t}" → notification coins independent across volunteers, periods and types, inside the one `iIndepFun` family; reason: (3) on p.13, p.15 and the proof of Lemma 2 use independence; the product in (6) has no meaning without it
--   - encoding: an active notified volunteer draws Z; an inactive one is unaffected (p.9) → `Z_{v,t}` is a primitive for each (v, t), read only if v is active and notified at t (as on p.34); reason: same law of the process
--   - encoding: the online process, on an unnamed probability space → any probability space carrying measurable, jointly independent primitives with the stated laws; reason: the statement over all such spaces specializes to any realization of the model
--   - encoding: indices in [a] = {1, …, a} → `Fin a`, paper index = value + 1, a = 0 allowed; reason: Lean convention; at a = 0 the sums are empty and no instance of the source changes
--   - encoding: (6)–(8), computed by Algorithm 1, with an s = 0 term in (8) → `IsDP`, a hypothesis on (x̃, J) listing the equations, with the s = 0 term written λ_{0,t} J_{v,t+1}; reason: the equations have exactly one solution; variables of type 0 are 0 (fn. 18, p.16)
--   - encoding: Z > 0 with law g, τ ∈ ℕ → `g : ℕ → ℝ` with `g 0 = 0`, τ ranges over positive integers; reason: ℕ is {1, 2, …} in the source; same instances
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, §4.2, p.21 (closing paragraph of the proof of Theorem 1)

import Mathlib
import Definitions.Def_VolunteerNotify_IsExAnte
import Definitions.Def_VolunteerNotify_IsDP
import Definitions.Def_VolunteerNotify_Process

open MeasureTheory

namespace VolunteerNotify

/-- The closing step of §4.2, Manshadi–Rodilitz, arXiv:2002.08474v7, p.21: the expected total
number of tasks completed under the SN policy is at least `(1/(2 − q)) f(x*)`. -/
theorem closing_step {V S T : ℕ} (I : Instance V S T) (xstar xt : Decision V S T)
    (J : Fin V → Fin (T + 1) → ℝ) (hx : IsExAnte I xstar) (hdp : IsDP I xstar xt J)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Process I xt μ) : 1 / (2 - mdhr I.g) * f I xstar ≤ POL P := by sorry

end VolunteerNotify
