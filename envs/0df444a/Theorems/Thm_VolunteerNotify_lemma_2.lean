-- Prove2me | Theorems.Thm_VolunteerNotify_lemma_2
-- name    : VolunteerNotify.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:38:30.252964+00:00
-- url     : https://prove2.me/theorems/2deed769-72f9-4c49-9495-be7c69401a42
-- title:
--   Lemma 2 — the contribution of $v$ under the SN policy is at least $J_{v,1}$
-- statement:
--   Let $x\in[0,1]^{V\times S\times T}$, let $(\tilde x,J)$ solve (6)–(8) for the input $x$, and consider the online process that notifies with probabilities $\tilde x$. Under the index-based priority scheme, for every volunteer $v$,
--   $$
--   \mathbb E\Bigl[\sum_{t=1}^T\mathbb 1\{v=\min\mathrm{Resp}(t)\}\Bigr]\ge J_{v,1}.
--   $$
--   This reduces the analysis of the correlated online process to the deterministic recursion (8).
--
--   Differences from the source:
--   - generalization: the offline phase is run on x* of (5) → any input x ∈ [0,1]^{V×S×T}; reason: x* ∈ [0,1]^{V×S×T}, so the statement specializes to the source
--   - reading: Algorithm 1: "Notify v with probability x̃_{v,s,t}" → notification coins independent across volunteers, periods and types, inside the one `iIndepFun` family; reason: (3) on p.13, p.15 and the proof of Lemma 2 use independence; the product in (6) has no meaning without it
--   - encoding: an active notified volunteer draws Z; an inactive one is unaffected (p.9) → `Z_{v,t}` is a primitive for each (v, t), read only if v is active and notified at t (as on p.34); reason: same law of the process
--   - encoding: the online process, on an unnamed probability space → any probability space carrying measurable, jointly independent primitives with the stated laws; reason: the statement over all such spaces specializes to any realization of the model
--   - encoding: indices in [a] = {1, …, a} → `Fin a`, paper index = value + 1, a = 0 allowed; reason: Lean convention; at a = 0 the sums are empty and no instance of the source changes
--   - encoding: (6)–(8), computed by Algorithm 1, with an s = 0 term in (8) → `IsDP`, a hypothesis on (x̃, J) listing the equations, with the s = 0 term written λ_{0,t} J_{v,t+1}; reason: the equations have exactly one solution; variables of type 0 are 0 (fn. 18, p.16)
--   - encoding: Z > 0 with law g, τ ∈ ℕ → `g : ℕ → ℝ` with `g 0 = 0`, τ ranges over positive integers; reason: ℕ is {1, 2, …} in the source; same instances
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, Lemma 2, p.17

import Mathlib
import Definitions.Def_VolunteerNotify_IsDP
import Definitions.Def_VolunteerNotify_Process

open MeasureTheory

namespace VolunteerNotify

/-- Lemma 2, Manshadi–Rodilitz, arXiv:2002.08474v7, p.17: under the index-based priority scheme
and the SN policy, the contribution of volunteer `v` is at least `J_{v,1}`.

**Formalization Note.** The offline phase is run on any input `x ∈ [0,1]^{V×S×T}`; the paper's
`x*` is one such input. `J v 0` is `J_{v,1}`, and `P` is the online process with `w = x̃`. -/
theorem lemma_2 {V S T : ℕ} (I : Instance V S T) (x xt : Decision V S T)
    (J : Fin V → Fin (T + 1) → ℝ) (hx : ∀ v s t, x v s t ∈ Set.Icc (0 : ℝ) 1)
    (hdp : IsDP I x xt J) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (P : Process I xt μ) (v : Fin V) : J v 0 ≤ contribution P v := by sorry

end VolunteerNotify
