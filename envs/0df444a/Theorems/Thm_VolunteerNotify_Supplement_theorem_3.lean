-- Prove2me | Theorems.Thm_VolunteerNotify_Supplement_theorem_3
-- name    : VolunteerNotify.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:29:26.531725+00:00
-- url     : https://prove2.me/theorems/2241b7da-1e3a-4c3c-849d-3f6a8f3dae21
-- title:
--   Theorem 3 — the scaled-down notification policy is $\frac1{2-q}(1-\frac1e)$-competitive
-- statement:
--   Let $\mathcal I$ be any instance of the online volunteer notification problem, and let $q$ be the MDHR of its inter-activity time distribution. Let $x^*$ be the ex ante solution (5), and let the online phase of Algorithm 2 notify each volunteer $v$ independently with probability $\frac{x^*_{v,s,t}}{(2-q)\beta_{v,t}}$ when a task of type $s$ arrives at $t$, with $\beta$ as in Algorithm 2. Then
--   $$
--   \mathrm{POL}_{\mathcal I}\ge\frac1{2-q}\Big(1-\frac1e\Big)\mathrm{LP}_{\mathcal I}.
--   $$
--   The SDN policy thus has the same competitive ratio as the SN policy of Theorem 1, with a simpler offline phase (no dynamic programs), although the paper reports that it performs worse numerically.
--
--   **Formalization Note** The statement is for every instance, every value of (5) and every probability space carrying the process, in the form of the published Theorem 1.
--
--   Differences from the source:
--   - generalization: q is the minimum over τ ∈ ℕ of the hazard rates (Definition 1) → q is their infimum (`mdhr`); reason: the minimum need not exist; the infimum equals it whenever it exists, so the statement specializes to the source (the published convention of the goal)
--   - generalization: x* is the argmax of f over the three candidates of (5) → `IsExAnte`: every value of (5) over any optimizer of (LP), any m ≥ 1 and Frank–Wolfe run, any solution of (SQ-v), and any tie-break; reason: the candidates are not unique; each run of the source is one such value
--   - reading: Algorithm 2: "Notify v with probability x*_{v,s,t}/((2−q)β_{v,t})" → notification coins independent across volunteers, periods and types, inside the published `Process` (one `iIndepFun` family); reason: Appendix E calls the SDN policy one that "independently notifies volunteers" (p.45); the proofs of Lemmas 7–8 use independence
--   - encoding: the online process, on an unnamed probability space → any probability space carrying the published `Process I (sdnProb I x) μ`; reason: the statement over all such spaces specializes to any realization of the model
--   - encoding: LP_I is the maximum of (LP) → `lpValue` is the `sSup` of the objective over P; reason: P is nonempty and compact and the objective is continuous, so the supremum is attained
--   - encoding: indices in [a] = {1, …, a} → `Fin a`, paper index = value + 1; reason: Lean convention; same instances
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, Theorem 3, p.46; Algorithm 2, p.46; Definition 3, p.12

import Mathlib
import Definitions.Def_VolunteerNotify_IsExAnte
import Definitions.Def_VolunteerNotify_Process
import Definitions.Def_VolunteerNotify_Supplement_sdnProb

open MeasureTheory

namespace VolunteerNotify.Supplement

/-- Theorem 3, Manshadi–Rodilitz, arXiv:2002.08474v7, p.46: if the MDHR of the inter-activity time
distribution is `q`, then the scaled-down notification policy of Algorithm 2 is
`(1/(2 − q))(1 − 1/e)`-competitive, that is (Definition 3, p.12), for every instance `I`,
`POL_I ≥ (1/(2 − q))(1 − 1/e) LP_I`.

**Formalization Note.** The offline phase is `IsExAnte I xstar` (5) and `sdnBeta`; the online
phase is `P`, the process notifying independently with probabilities `sdnProb I xstar`. The
statement is for every instance, every value of (5), and every probability space carrying the
process, exactly as the published Theorem 1. -/
theorem theorem_3 {V S T : ℕ} (I : Instance V S T) (xstar : Decision V S T)
    (hx : IsExAnte I xstar) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (P : Process I (sdnProb I xstar) μ) :
    1 / (2 - mdhr I.g) * (1 - 1 / Real.exp 1) * lpValue I ≤ POL P := by sorry

end VolunteerNotify.Supplement
