-- Prove2me | Theorems.Thm_WiesemannRMDP_SRect_Supplement_lemma_C_1
-- name    : WiesemannRMDP.SRect.Supplement.lemma_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:54:40.267979+00:00
-- url     : https://prove2.me/theorems/eb79d6ef-7146-4c93-b793-5a72544d36d2
-- title:
--   Lemma C.1 — under (A1), (A2) the transition frequencies n_sas′/n converge a.s. to π0(a|s)p^{ξ0}(s′|s,a)/µ_s, with µ_s ∈ [1, ∞)
-- statement:
--   In the setting of Theorem 5.3 (structural model under the standing assumptions (3), true parameter $\xi^0$, historical stationary policy $\pi_0$, observation process $(s_t,a_t)_{t\ge1}$), let $n_{sas'}$ be the number of transitions $(s_t,a_t,s_{t+1})=(s,a,s')$, $t\le n-1$, in the observation of length $n$, and let $\mu_s$ be the expected return time of $s$ in the Markov chain on $\mathcal S$ with kernel $\widehat P(\pi_0;\xi^0)$ of (7a). Under (A1) $\xi^0\in\operatorname{int}\Xi_0$ and (A2) $\widehat P(\pi_0;\xi)$ is irreducible for some $\xi\in\Xi_0$:
--
--   1. $\mu_s\in[1,\infty)$ for every $s\in\mathcal S$;
--   2. almost surely, for all $(s,a,s')\in\mathcal S\times\mathcal A\times\mathcal S$,
--   $$\frac{n_{sas'}}{n}\ \xrightarrow[n\to\infty]{}\ \frac{\pi_0(a\mid s)\,p^{\xi^0}(s'\mid s,a)}{\mu_s}. \tag{47}$$
--
--   The lemma identifies the limit of the normalized matrix (37c) and hence the matrix $\Sigma$ of (48d) used in the proof of Theorem 5.5.
--
--   **Formalization Note** $\mu_s$ is valued in $[0,\infty]$ and computed by the tail-sum formula $\mathbb E_s[\tau_s^+]=\sum_{m\ge0}\mathbb P_s(\tau_s^+>m)$; the limit uses its real value, which is the paper's under item 1.
--
--   Differences from the source:
--
--   - generalization: (Ω, F, P) is the canonical space (S × A)^∞ with the product measure induced by π0 and P0 → any probability space with a process whose finite paths have the probabilities (32) at ξ0; reason: the conclusion depends only on the law of the observations, and the canonical space is one such space
--   - encoding: (47) holds almost surely for each (s, a, s′) → one almost-sure event for all triples; reason: there are finitely many triples, so the two are equivalent
--   - encoding: the observation (s1, a1, …, sn, an) → X 0, …, X (n − 1); reason: Lean's time index starts at 0
--   - reading: "the MDP" of §5.1 satisfies definition (3) → the whole of Model.Standing is assumed; reason: r, λ do not occur in Lemma C.1, so no instance is lost
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), p. 49, Lemma C.1 (47); expected return time p. 49; (A1) p. 29; (A2) p. 32

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_WiesemannRMDP_SRect_Model
import Definitions.Def_WiesemannRMDP_SRect_Supplement_Chains
import Definitions.Def_WiesemannRMDP_SRect_Supplement_Inference

open MeasureTheory ProbabilityTheory Filter FoundationsML.ReinforcementLearning Matrix
open scoped Topology ENNReal

namespace WiesemannRMDP.SRect.Supplement

open WiesemannRMDP.SRect

/-- Lemma C.1 (Wiesemann, Kuhn & Rustem, *Robust Markov Decision Processes*, Optimization Online
2610, revision of February 9, 2012, p. 49): under the assumptions (A1) and (A2),
`n_{sas'}/n → π0(a|s) p^{ξ0}(s'|s, a) / µ_s` almost surely for all `(s, a, s') ∈ S × A × S` (47),
where `µ_s ∈ [1, ∞)` denotes the expected return time of state `s` under policy `π0`.

**Formalization Note.** `µ_s` is `returnTime M π0 ξ0 s`, valued in `ℝ≥0∞`; the claim
`µ_s ∈ [1, ∞)` is part of the conclusion. The almost-sure event is taken simultaneously for all
triples (there are finitely many). -/
theorem lemma_C_1 {St Act : Type*} [Fintype St] [DecidableEq St] [Fintype Act]
    [DecidableEq Act] [Nonempty St] [Nonempty Act] {q L : ℕ} (M : Model St Act q L)
    (hM : M.Standing) (π0 : St → Act → ℝ) (hπ0 : IsPolicy π0)
    (ξ0 : Fin q → ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → St × Act) (hX : IsObservationProcess M π0 ξ0 P X)
    (hA1 : A1 M ξ0) (hA2 : A2 M π0) :
    (∀ s : St, 1 ≤ returnTime M π0 ξ0 s ∧ returnTime M π0 ξ0 s < ∞) ∧
    ∀ᵐ ω ∂P, ∀ (s : St) (a : Act) (s' : St),
      Tendsto (fun n : ℕ => (transCount X n ω s a s' : ℝ) / n) atTop
        (𝓝 (π0 s a * M.pXi ξ0 s a s' / (returnTime M π0 ξ0 s).toReal)) := by sorry

end WiesemannRMDP.SRect.Supplement
