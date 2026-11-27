-- Prove2me | Theorems.Thm_VolunteerNotify_Supplement_lemma_7
-- name    : VolunteerNotify.Supplement.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:28:08.366676+00:00
-- url     : https://prove2.me/theorems/f5779d7a-39a6-4a7b-b381-946959f1e0c1
-- title:
--   Lemma 7 — under the SDN policy, $v$ is active at $t$ with probability $\beta_{v,t}\ge\frac1{2-q}$
-- statement:
--   Let $\mathcal I$ be an instance with MDHR $q$, let $x\in\mathcal P$, and consider the SDN policy of Algorithm 2 built from $x$: $\beta_{v,1}=1$, $\beta_{v,t}=1-\sum_{t'<t}\sum_s\lambda_{s,t'}\frac{x_{v,s,t'}}{2-q}(1-G(t-t'))$, and, when a task of type $s$ arrives at $t$, each volunteer $v$ is notified independently with probability $\frac{x_{v,s,t}}{(2-q)\beta_{v,t}}$. Let $E_{v,t}$ be the event that $v$ is active in period $t$. Then for all $v\in[V]$ and $t\in[T]$:
--
--   1. $\mathbb P(E_{v,t})=\beta_{v,t}$;
--   2. $\beta_{v,t}\ge\dfrac1{2-q}$.
--
--   The second part shows that the notification probabilities lie in $[0,1]$, so the SDN policy is well defined; the first is what makes each volunteer active and notified with probability $x_{v,s,t}/(2-q)$.
--
--   **Formalization Note** The online phase is any probability space carrying the published `Process` with the SDN probabilities. Algorithm 2 uses $x^*$ of (5), which lies in $\mathcal P$; the proof uses only $x\in\mathcal P$.
--
--   Differences from the source:
--   - generalization: the SDN policy built from x* of (5) → built from any x ∈ P; reason: the proof (p.47) uses only x* ∈ P; x* is one such x (published exAnte_feasible)
--   - generalization: q is the minimum over τ ∈ ℕ of the hazard rates (Definition 1) → q is their infimum (`mdhr`); reason: the minimum need not exist; the infimum equals it whenever it exists, so the statement specializes to the source (the published convention of the goal)
--   - reading: Algorithm 2: "Notify v with probability x*_{v,s,t}/((2−q)β_{v,t})" → notification coins independent across volunteers, periods and types, inside the published `Process` (one `iIndepFun` family); reason: Appendix E calls the SDN policy one that "independently notifies volunteers" (p.45); the proofs of Lemmas 7–8 use independence
--   - encoding: the online process, on an unnamed probability space → any probability space carrying the published `Process I (sdnProb I x) μ`; reason: the statement over all such spaces specializes to any realization of the model
--   - encoding: indices in [a] = {1, …, a} → `Fin a`, paper index = value + 1; reason: Lean convention; same instances
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, Lemma 7, p.47; Algorithm 2, p.46

import Mathlib
import Definitions.Def_VolunteerNotify_lpValue
import Definitions.Def_VolunteerNotify_Process
import Definitions.Def_VolunteerNotify_Supplement_sdnProb

open MeasureTheory

namespace VolunteerNotify.Supplement

/-- Lemma 7, Manshadi–Rodilitz, arXiv:2002.08474v7, p.47: for the SDN policy of Algorithm 2, let
`E_{v,t}` be the event that volunteer `v` is active in period `t`. Then `P(E_{v,t}) = β_{v,t}` for
all `v ∈ [V]` and `t ∈ [T]`; further, `β_{v,t} ≥ 1/(2 − q)`.

**Formalization Note.** The SDN policy is built from any `x ∈ P` (Algorithm 2 uses `x* ∈ P`; the
proof uses only `x ∈ P`). Its online phase is any probability space carrying `Process I w μ` with
`w = sdnProb I x`. The second clause makes `w ∈ [0, 1]`, so such processes exist (e.g. on the
product of the primitive laws) and the first clause is not vacuous. -/
theorem lemma_7 {V S T : ℕ} (I : Instance V S T) (x : Decision V S T) (hx : x ∈ feasibleSet I)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Process I (sdnProb I x) μ) :
    (∀ v t, μ.real {ω | IsActive (fun i => P.prim i ω) v t} = sdnBeta I x v t) ∧
      ∀ v t, 1 / (2 - mdhr I.g) ≤ sdnBeta I x v t := by sorry

end VolunteerNotify.Supplement
