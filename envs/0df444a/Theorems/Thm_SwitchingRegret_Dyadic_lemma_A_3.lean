-- Prove2me | Theorems.Thm_SwitchingRegret_Dyadic_lemma_A_3
-- name    : SwitchingRegret.Dyadic.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:27:42.018918+00:00
-- url     : https://prove2.me/theorems/55e481c8-75f1-4195-bfca-f2597cb7af98
-- title:
--   Lemma A.3 — uniform prefix bound for denominator terms
-- statement:
--   Let $T>K\ge2$, let $\ell\in[0,1]^{T\times K}$ be deterministic before any seed is drawn, and let $u$ be a deterministic arm sequence with at most $S<T$ switches. For any deterministic $j,\tau\in\{1,\ldots,T\}$, run the fresh rate-$\eta_j$ continuation from round $\tau$. Let $\rho$ be its first threshold crossing, or $T$, with the crossing round included. Fix the routing bits, main-action uniforms and interval-rate uniforms to any values in their support. Probability below is only over the independent challenge-action uniforms. For every $0<\varepsilon<1$, except on a failure event of measure at most $\varepsilon$, simultaneously for all $n\in[\tau,T]$,
--   $$\sum_{t=\tau}^n D_t\le3\Gamma_j+\frac32\log(1/\varepsilon).$$
--   Here $D_t$ is Eq. (48), zero on main rounds, and $\Gamma_j$ uses every interval scheduled from $\tau$ through $T$. The single failure event is the existence of any violating endpoint.
--
--   Differences from the source:
--   - encoding: arms in [K] and finite round sequences → arms in Fin K and natural-indexed functions restricted to rounds 1 through T; reason: relabeling is bijective and values outside the horizon are ignored; NeZero K follows from K ≥ 2
--   - encoding: Algorithm 1 argmin updates and independent Bernoulli and uniform draws → the paper’s normalized exponential closed forms and a finite product of independent uniform coordinates with threshold routing; reason: PDF pp. 20 and 25 derive the closed forms; Appendix A.1 gives this seed law, with unused coordinates integrating out
--   - generalization: conditional on the start history of a reached epoch → every deterministic j and tau in {1,...,T}, under fresh epoch seeds; reason: the reset state depends only on j and tau and the assigned epoch seeds are independent of the past
--   - generalization: conditional on the enlarged rate history, with a measurable interval family → every fixed routing, main-seed and rate realization in its support, followed by any admissible fixed family, under fresh challenge seeds; reason: this includes every conditional-history value and every family measurable in that history
--   - encoding: probability at least one minus the stated error → outer measure of the failure event at most that error; reason: the inequalities are measurable functions of finite seed products; the failure form also avoids a nonmeasurable-good-event loophole
-- source:
--   Mengxiao Zhang, Toward Optimal Switching Regret for Multi-Armed Bandits with Oblivious Adversary, 2026 preprint, STOC 2027 submission #99, SHA-256 70dc03d632eeb5878823d984fc755157b34301d8189bbd7a6087570a8f8a7fee, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/99.pdf, Lemma A.3, PDF p. 29 (printed p. 28).

import Definitions.Def_SwitchingRegret_Dyadic_Continuation

open MeasureTheory

namespace SwitchingRegret.Dyadic

theorem lemma_A_3
    {K T : ℕ} [NeZero K] (hK : 2 ≤ K) (hT : K < T)
    (ell : LossTable K) (hell : validLoss T ell)
    (j tau : ℕ) (hj : j ∈ Finset.Icc 1 T) (htau : tau ∈ Finset.Icc 1 T)
    (f : FixedSeeds T) (hf : f.valid) (ε : ℝ) (he : 0 < ε) (he1 : ε < 1) :
    (challengeLaw T) {v | ∃ n ∈ Finset.Icc tau T,
      3 * Gamma K T j tau (assemble f v) + (3 / 2 : ℝ) * Real.log (1 / ε) <
        denominatorSum ell j tau (assemble f v) n} ≤ ENNReal.ofReal ε := by sorry

end SwitchingRegret.Dyadic
