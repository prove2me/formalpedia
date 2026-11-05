-- Prove2me | Theorems.Thm_VolunteerNotify_theorem_1
-- name    : VolunteerNotify.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:39:45.466968+00:00
-- url     : https://prove2.me/theorems/5db84ded-85b3-468d-a5f1-269f968e3017
-- title:
--   Theorem 1 — the sparse notification policy is $\frac1{2-q}(1-\frac1e)$-competitive
-- statement:
--   Let $\mathcal I$ be any instance of the online volunteer notification problem, and let $q$ be the MDHR of its inter-activity time distribution. Let $x^*$ be the ex ante solution (5), let $(\tilde x,J)$ be the solution of the dynamic programs (6)–(8) for $x^*$, and let the online phase of Algorithm 1 notify each volunteer $v$ with probability $\tilde x_{v,s,t}$ when a task of type $s$ arrives at $t$. Then the expected number of completed tasks satisfies
--   $$
--   \mathrm{POL}_{\mathcal I}\ge\frac1{2-q}\Bigl(1-\frac1e\Bigr)\mathrm{LP}_{\mathcal I}.
--   $$
--   This is the main guarantee of the source. It is parameterized by $q$, improves as $q$ grows, and gives $\frac12(1-\frac1e)$ for every inter-activity time distribution. There are no bounds on $V,S,T$ and no restriction on $g$ beyond being a probability law on $\{1,2,\dots\}$.
--
--   Differences from the source:
--   - generalization: q is the minimum over τ ∈ ℕ of the hazard rates (Definition 1) → q is their infimum (`mdhr`); reason: the minimum need not exist, e.g. hazards 1/2 + 1/(τ+2); the infimum equals the minimum whenever it exists, so the statement specializes to the source
--   - generalization: x* is the argmax of f over the three candidates of (5) → `IsExAnte`: every value of (5) over any optimizer of (LP), any m ≥ 1 and Frank–Wolfe run, any solution of (SQ-v), and any tie-break; reason: the candidates are not unique; each run of the source is one such value
--   - reading: Algorithm 1: "Notify v with probability x̃_{v,s,t}" → notification coins independent across volunteers, periods and types, inside the one `iIndepFun` family; reason: (3) on p.13, p.15 and the proof of Lemma 2 use independence; the product in (6) has no meaning without it
--   - encoding: an active notified volunteer draws Z; an inactive one is unaffected (p.9) → `Z_{v,t}` is a primitive for each (v, t), read only if v is active and notified at t (as on p.34); reason: same law of the process
--   - encoding: the online process, on an unnamed probability space → any probability space carrying measurable, jointly independent primitives with the stated laws; reason: the statement over all such spaces specializes to any realization of the model
--   - encoding: Z > 0 with law g, τ ∈ ℕ → `g : ℕ → ℝ` with `g 0 = 0`, τ ranges over positive integers; reason: ℕ is {1, 2, …} in the source; same instances
--   - encoding: indices in [a] = {1, …, a} → `Fin a`, paper index = value + 1, a = 0 allowed; reason: Lean convention; at a = 0 the sums are empty and no instance of the source changes
--   - encoding: (6)–(8), computed by Algorithm 1, with an s = 0 term in (8) → `IsDP`, a hypothesis on (x̃, J) listing the equations, with the s = 0 term written λ_{0,t} J_{v,t+1}; reason: the equations have exactly one solution; variables of type 0 are 0 (fn. 18, p.16)
--   - encoding: LP_I is the maximum of (LP) → `lpValue` is the `sSup` of the objective over P; reason: P is nonempty and compact and the objective is continuous, so the supremum is attained and equals the maximum
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, Theorem 1, p.16; Definition 3, p.12; Algorithm 1, p.17

import Mathlib
import Definitions.Def_VolunteerNotify_IsExAnte
import Definitions.Def_VolunteerNotify_IsDP
import Definitions.Def_VolunteerNotify_Process

open MeasureTheory

namespace VolunteerNotify

/-- Theorem 1, Manshadi–Rodilitz, arXiv:2002.08474v7, p.16: if the MDHR of the inter-activity
time distribution is `q`, then the sparse notification policy of Algorithm 1 is
`(1/(2 − q))(1 − 1/e)`-competitive, that is (Definition 3, p.12), for every instance `I`,
`POL_I ≥ (1/(2 − q))(1 − 1/e) LP_I`.

**Formalization Note.** The offline phase of Algorithm 1 is `IsExAnte I xstar` (5) and
`IsDP I xstar xt J` (6)–(8). The online phase is `P`, the process with `w = x̃`. The statement is
for every instance, every value of (5), and every probability space carrying the process. -/
theorem theorem_1 {V S T : ℕ} (I : Instance V S T) (xstar xt : Decision V S T)
    (J : Fin V → Fin (T + 1) → ℝ) (hx : IsExAnte I xstar) (hdp : IsDP I xstar xt J)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Process I xt μ) :
    1 / (2 - mdhr I.g) * (1 - 1 / Real.exp 1) * lpValue I ≤ POL P := by sorry

end VolunteerNotify
