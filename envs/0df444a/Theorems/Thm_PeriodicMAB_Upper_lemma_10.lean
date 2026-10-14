-- Prove2me | Theorems.Thm_PeriodicMAB_Upper_lemma_10
-- name    : PeriodicMAB.Upper.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:54.285294+00:00
-- url     : https://prove2.me/theorems/9dd4a3b3-09e1-4ae4-aafa-49f19cd9cb46
-- title:
--   Lemma 10, p. 22 — on $\mathcal E$ the optimal arm survives screening, and the oracle's per-epoch gap is $\le1$, $8\sigma/2^s$ or $2\sigma/\sqrt T$
-- statement:
--   Assume Assumption 1, Assumption 3, $nK\le T$, $\delta\in(0,1)$, and let every arm have a mean sequence of minimum period $T_k$. Suppose the event $\mathcal E$ of Lemma 9 holds, and that at the epoch $t\in\{nK+1,\dots,T\}$ the oracle chooses arm $\tilde\pi_t$ in round $s$ of Algorithm 2. Let $\pi^*_t$ be any optimal arm, $\mu_{\pi^*_t,t}=\max_k\mu_{k,t}$. Then
--
--   1. the optimal arm is never excluded during screening: $\pi^*_t\in\mathcal A_{s'}$ for all $s'\le s$;
--   2. if $\tilde\pi_t$ is chosen in Step 9 with $s=1$, then $\mu_{\pi^*_t,t}-\mu_{\tilde\pi_t,t}\le1$;
--   3. if $\tilde\pi_t$ is chosen in Step 9 with $s\ge2$, then $\mu_{\pi^*_t,t}-\mu_{\tilde\pi_t,t}\le 8\sigma/2^s$;
--   4. if $\tilde\pi_t$ is chosen in Step 12, then $\mu_{\pi^*_t,t}-\mu_{\tilde\pi_t,t}\le 2\sigma/\sqrt T$.
--
--   These per-epoch regret bounds are summed over the rounds in the proof of Lemma 11.
--
--   **Formalization Note** The statement is pathwise: it holds for every noise realization in $\mathcal E$. The paper's $\pi^*_t=\arg\max_k\mu_{k,t}$ is read as any maximizer. "Chosen in Step 12" is the record `step9 = false` of the oracle's decision at $t$; the fallback of an exhausted tournament also carries that record but cannot occur here, since Assumption 3 gives $T>4$. Assumption 3, $nK\le T$, the period hypothesis and $\delta\in(0,1)$ are standing assumptions of §4 and Algorithm 2.
-- source:
--   Chen, Wang and Wang, Learning and Optimization with Seasonal Patterns, arXiv:2005.08088v4, p. 22, Lemma 10

import Mathlib
import Definitions.Def_PeriodicMAB_Upper_Model
import Definitions.Def_PeriodicMAB_Upper_Spectral
import Definitions.Def_PeriodicMAB_Upper_Policy

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace PeriodicMAB.Upper

/-- Lemma 10 (p. 22): on the event `ℰ`, if the oracle chooses arm `a` at the stage-two epoch
`t` in round `s` (in Step 9 if `step9`, in Step 12 otherwise), then for every optimal arm
`k*` of epoch `t`: (1) `k* ∈ 𝒜_{s'}` for all `s' ≤ s`; (2) Step 9 with `s = 1` gives
`µ_{k*,t} − µ_{a,t} ≤ 1`; (3) Step 9 with `s ≥ 2` gives `≤ 8σ/2^s`; (4) Step 12 gives `≤ 2σ/√T`. -/
theorem lemma_10 {Ω : Type*} (ε : ℕ → Ω → ℝ) (σ : ℝ≥0) (hσ : 0 < σ)
    {K : ℕ} [NeZero K] (μ : Fin K → ℕ → ℝ) (Tper : Fin K → ℕ) (T n g : ℕ) (δ : ℝ)
    (hper : ∀ k, IsMinPeriod (μ k) (Tper k)) (hA1 : Assumption1 μ T)
    (hA3 : Assumption3 T n g Tper) (hnK : n * K ≤ T) (hδ : 0 < δ) (hδ1 : δ < 1)
    (ω : Ω) (hω : ω ∈ eventE μ ε σ δ T n Tper) (t : ℕ) (ht : t ∈ Icc (n * K + 1) T)
    (a : Fin K) (s : ℕ) (step9 : Bool)
    (hdec : decisionAt σ δ T n Tper (reward μ ε ω) t = (a, s, step9))
    (kstar : Fin K) (hstar : ∀ k, μ k t ≤ μ kstar t) :
    (∀ s' ∈ Icc 1 s, kstar ∈ activeAt σ δ T n Tper (reward μ ε ω) s' t) ∧
    (step9 = true → s = 1 → μ kstar t - μ a t ≤ 1) ∧
    (step9 = true → 2 ≤ s → μ kstar t - μ a t ≤ 8 * σ / 2 ^ s) ∧
    (step9 = false → μ kstar t - μ a t ≤ 2 * σ / Real.sqrt T) := by sorry

end PeriodicMAB.Upper
