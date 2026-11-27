-- Prove2me | Theorems.Thm_VolunteerNotify_Supplement_lemma_8
-- name    : VolunteerNotify.Supplement.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:28:36.576438+00:00
-- url     : https://prove2.me/theorems/2f89b6ff-4d51-4557-b5be-2e3194cb9617
-- title:
--   Lemma 8 — contribution of a volunteer under the SDN policy is at least $\frac1{2-q}f_v(x)$
-- statement:
--   Let $\mathcal I$ be an instance with MDHR $q$ and let $x\in\mathcal P$. Under the SDN policy of Algorithm 2 built from $x$ and the index-based priority scheme (Definition 4: of the volunteers who respond, the one with the smallest index completes the task), the contribution of every volunteer $v\in[V]$, the expected number of tasks she completes, is at least
--   $$
--   \frac1{2-q}f_v(x),\qquad f_v(x)=\sum_{t=1}^T\sum_{s=1}^S\lambda_{s,t}\Big(\prod_{u<v}(1-p_{u,s}x_{u,s,t})\Big)p_{v,s}x_{v,s,t}.
--   $$
--   Summed over $v$ (Lemma 1) this gives the bound $\frac1{2-q}f(x^*)$ on the SDN policy's expected number of completed tasks, the key step of Theorem 3.
--
--   **Formalization Note** The policy is built from the same $x$ that appears in $f_v(x)$, as in the proof, where $x^*$ plays both roles.
--
--   Differences from the source:
--   - reading: "Under … the SDN policy, for any x ∈ P, the contribution … is at least (1/(2−q)) f_v(x)", while Algorithm 2 builds the policy from x* → the SDN policy built from the same x ∈ P; reason: the proof uses x* in both places; with the policy built from x* and x arbitrary the inequality is false in general (the reading of the published Lemma 3)
--   - generalization: q is the minimum over τ ∈ ℕ of the hazard rates (Definition 1) → q is their infimum (`mdhr`); reason: the minimum need not exist; the infimum equals it whenever it exists, so the statement specializes to the source (the published convention of the goal)
--   - reading: Algorithm 2: "Notify v with probability x*_{v,s,t}/((2−q)β_{v,t})" → notification coins independent across volunteers, periods and types, inside the published `Process` (one `iIndepFun` family); reason: Appendix E calls the SDN policy one that "independently notifies volunteers" (p.45); the proofs of Lemmas 7–8 use independence
--   - encoding: the online process, on an unnamed probability space → any probability space carrying the published `Process I (sdnProb I x) μ`; reason: the statement over all such spaces specializes to any realization of the model
--   - encoding: indices in [a] = {1, …, a} → `Fin a`, paper index = value + 1; reason: Lean convention; same instances
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, Lemma 8, p.48; Algorithm 2, p.46; Definition 4, p.13; (4), p.14

import Mathlib
import Definitions.Def_VolunteerNotify_lpValue
import Definitions.Def_VolunteerNotify_f
import Definitions.Def_VolunteerNotify_Process
import Definitions.Def_VolunteerNotify_Supplement_sdnProb

open MeasureTheory

namespace VolunteerNotify.Supplement

/-- Lemma 8, Manshadi–Rodilitz, arXiv:2002.08474v7, p.48: under the index-based priority scheme
(Definition 4) and the SDN policy, for any `x ∈ P`, the contribution of volunteer `v ∈ [V]`, the
expected number of tasks she completes, is at least `(1/(2 − q)) f_v(x)`.

**Formalization Note.** The SDN policy is built from the same `x` (`w = sdnProb I x`), as in the
proof, where `x*` plays both roles; with the policy built from a fixed `x*` and `x` arbitrary the
inequality is false in general (the same reading as the published Lemma 3). -/
theorem lemma_8 {V S T : ℕ} (I : Instance V S T) (x : Decision V S T) (hx : x ∈ feasibleSet I)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Process I (sdnProb I x) μ) (v : Fin V) :
    1 / (2 - mdhr I.g) * fv I x v ≤ contribution P v := by sorry

end VolunteerNotify.Supplement
