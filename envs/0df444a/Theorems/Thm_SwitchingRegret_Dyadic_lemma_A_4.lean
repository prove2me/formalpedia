-- Prove2me | Theorems.Thm_SwitchingRegret_Dyadic_lemma_A_4
-- name    : SwitchingRegret.Dyadic.lemma_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:27:53.504634+00:00
-- url     : https://prove2.me/theorems/8b4038dc-1fbd-473f-b71b-7abdf7119861
-- title:
--   Lemma A.4 — estimated versus true interval advantages
-- statement:
--   Let $T>K\ge2$, let $\ell\in[0,1]^{T\times K}$ be deterministic before any seed is drawn, and let $u$ be a deterministic arm sequence with at most $S<T$ switches. For any deterministic $j,\tau\in\{1,\ldots,T\}$, run the fresh rate-$\eta_j$ continuation from round $\tau$. Let $\rho$ be its first threshold crossing, or $T$, with the crossing round included. Fix the routing bits, main-action uniforms and interval-rate uniforms to any values in their support. Probability below is only over the independent challenge-action uniforms. Let $\mathcal S_j\subseteq\mathcal J_j$ be any disjoint family chosen after these fixed values, with $u_t=a_J$ throughout each $J$. For $0<\varepsilon<1/2$, except on a failure event of measure at most $2\varepsilon$, simultaneously for every $n\in[\tau,T]$,
--   $$\alpha\sum_{J\in\mathcal S_j}\sum_{t\in J,\ t\le n,\ b_t=0}(\langle q_t,\widehat\ell_{t,J}\rangle-\widehat\ell_{t,J,a_J})\ge\alpha\sum_{J\in\mathcal S_j}A_J(n)-\sum_{J\in\mathcal S_j}\frac\alpha{\eta_J}\log\frac{2TK}{\varepsilon}-\Gamma_j-2\alpha\sqrt{T\log(1/\varepsilon)}-\alpha\log(1/\varepsilon).$$
--   This retains all bias and fluctuation terms in the conversion from estimated to true advantage.
--
--   Differences from the source:
--   - encoding: arms in [K] and finite round sequences → arms in Fin K and natural-indexed functions restricted to rounds 1 through T; reason: relabeling is bijective and values outside the horizon are ignored; NeZero K follows from K ≥ 2
--   - encoding: Algorithm 1 argmin updates and independent Bernoulli and uniform draws → the paper’s normalized exponential closed forms and a finite product of independent uniform coordinates with threshold routing; reason: PDF pp. 20 and 25 derive the closed forms; Appendix A.1 gives this seed law, with unused coordinates integrating out
--   - generalization: the fixed optimal comparator u^(S) → every deterministic arm sequence with at most S switches; reason: the proof uses only the switch bound, and every minimizer is included
--   - generalization: conditional on the start history of a reached epoch → every deterministic j and tau in {1,...,T}, under fresh epoch seeds; reason: the reset state depends only on j and tau and the assigned epoch seeds are independent of the past
--   - generalization: conditional on the enlarged rate history, with a measurable interval family → every fixed routing, main-seed and rate realization in its support, followed by any admissible fixed family, under fresh challenge seeds; reason: this includes every conditional-history value and every family measurable in that history
--   - encoding: probability at least one minus the stated error → outer measure of the failure event at most that error; reason: the inequalities are measurable functions of finite seed products; the failure form also avoids a nonmeasurable-good-event loophole
-- source:
--   Mengxiao Zhang, Toward Optimal Switching Regret for Multi-Armed Bandits with Oblivious Adversary, 2026 preprint, STOC 2027 submission #99, SHA-256 70dc03d632eeb5878823d984fc755157b34301d8189bbd7a6087570a8f8a7fee, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/99.pdf, Lemma A.4, PDF p. 30 (printed p. 29).

import Definitions.Def_SwitchingRegret_Dyadic_Continuation

open MeasureTheory

namespace SwitchingRegret.Dyadic

theorem lemma_A_4
    {K T : ℕ} [NeZero K] (hK : 2 ≤ K) (hT : K < T)
    (ell : LossTable K) (hell : validLoss T ell)
    (S : ℕ) (hS : S < T) (u : ℕ → Fin K) (hu : switches T u ≤ S)
    (j tau : ℕ) (hj : j ∈ Finset.Icc 1 T) (htau : tau ∈ Finset.Icc 1 T)
    (f : FixedSeeds T) (hf : f.valid) (family : Finset (Dyad T))
    (hfamily : admissibleFamily tau u family) (ε : ℝ) (he : 0 < ε) (he1 : ε < 1 / 2) :
    (challengeLaw T) {v | ∃ n ∈ Finset.Icc tau T,
      familyAdvantage ell u j tau (assemble f v) family n -
        armPenalty (K := K) j (assemble f v) family (fun _ => 2 * (T : ℝ) * K / ε) -
        Gamma K T j tau (assemble f v) - 2 * alpha T * Real.sqrt (T * Real.log (1 / ε)) -
        alpha T * Real.log (1 / ε) > estimatedAdvantage ell u j tau (assemble f v) family n}
      ≤ ENNReal.ofReal (2 * ε) := by sorry

end SwitchingRegret.Dyadic
