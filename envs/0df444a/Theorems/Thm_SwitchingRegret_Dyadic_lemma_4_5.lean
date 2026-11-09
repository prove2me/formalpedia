-- Prove2me | Theorems.Thm_SwitchingRegret_Dyadic_lemma_4_5
-- name    : SwitchingRegret.Dyadic.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:27:26.306397+00:00
-- url     : https://prove2.me/theorems/b933bdad-fd21-4714-99e8-368c0562655b
-- title:
--   Lemma 4.5 — credit captures threshold-selected advantage
-- statement:
--   Let $T>K\ge2$, let $\ell\in[0,1]^{T\times K}$ be deterministic before any seed is drawn, and let $u$ be a deterministic arm sequence with at most $S<T$ switches. For any deterministic $j,\tau\in\{1,\ldots,T\}$, run the fresh rate-$\eta_j$ continuation from round $\tau$. Let $\rho$ be its first threshold crossing, or $T$, with the crossing round included. For each fixed endpoint $n\in[\tau,T]$, except on a failure event of measure at most $\delta_0=T^{-3}$,
--   $$C^{\rm cont}_{j,n}\ge\frac34 W_j(n)-\frac{KT\eta_j}{2}-4\Gamma_j.$$
--   The endpoint is fixed outside the probability statement. The threshold-selected advantage and the full continuation cost are computed on the same continuation.
--
--   Differences from the source:
--   - encoding: arms in [K] and finite round sequences → arms in Fin K and natural-indexed functions restricted to rounds 1 through T; reason: relabeling is bijective and values outside the horizon are ignored; NeZero K follows from K ≥ 2
--   - encoding: Algorithm 1 argmin updates and independent Bernoulli and uniform draws → the paper’s normalized exponential closed forms and a finite product of independent uniform coordinates with threshold routing; reason: PDF pp. 20 and 25 derive the closed forms; Appendix A.1 gives this seed law, with unused coordinates integrating out
--   - generalization: the fixed optimal comparator u^(S) → every deterministic arm sequence with at most S switches; reason: the proof uses only the switch bound, and every minimizer is included
--   - generalization: conditional on the start history of a reached epoch → every deterministic j and tau in {1,...,T}, under fresh epoch seeds; reason: the reset state depends only on j and tau and the assigned epoch seeds are independent of the past
--   - encoding: probability at least one minus the stated error → outer measure of the failure event at most that error; reason: the inequalities are measurable functions of finite seed products; the failure form also avoids a nonmeasurable-good-event loophole
-- source:
--   Mengxiao Zhang, Toward Optimal Switching Regret for Multi-Armed Bandits with Oblivious Adversary, 2026 preprint, STOC 2027 submission #99, SHA-256 70dc03d632eeb5878823d984fc755157b34301d8189bbd7a6087570a8f8a7fee, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/99.pdf, Lemma 4.5, PDF p. 13 (printed p. 12).

import Definitions.Def_SwitchingRegret_Dyadic_Continuation

open MeasureTheory

namespace SwitchingRegret.Dyadic

theorem lemma_4_5
    {K T : ℕ} [NeZero K] (hK : 2 ≤ K) (hT : K < T)
    (ell : LossTable K) (hell : validLoss T ell)
    (S : ℕ) (hS : S < T) (u : ℕ → Fin K) (hu : switches T u ≤ S)
    (j tau : ℕ) (hj : j ∈ Finset.Icc 1 T) (htau : tau ∈ Finset.Icc 1 T)
    (n : ℕ) (hn : n ∈ Finset.Icc tau T) :
    (epochLaw T) {xi | (3 / 4 : ℝ) * W ell u j tau xi n - (K : ℝ) * T * eta K T j / 2 -
      4 * Gamma K T j tau xi > continuationCredit ell j tau xi n} ≤ ENNReal.ofReal (delta0 T) := by sorry

end SwitchingRegret.Dyadic
