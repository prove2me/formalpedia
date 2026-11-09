-- Prove2me | Theorems.Thm_SwitchingRegret_Dyadic_lemma_4_1
-- name    : SwitchingRegret.Dyadic.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:27:49.776453+00:00
-- url     : https://prove2.me/theorems/278dd2a6-9e68-43aa-9b5f-cc0d5a7930a6
-- title:
--   Lemma 4.1 — main learner regret in an epoch
-- statement:
--   Let $T>K\ge2$, let $\ell\in[0,1]^{T\times K}$ be deterministic before any seed is drawn, and let $u$ be a deterministic arm sequence with at most $S<T$ switches. For any deterministic $j,\tau\in\{1,\ldots,T\}$, run the fresh rate-$\eta_j$ continuation from round $\tau$. Let $\rho$ be its first threshold crossing, or $T$, with the crossing round included. Write $H=\rho-\tau+1$. The stopped main regret and $H$ are integrable, and
--   $$\mathbb E[\operatorname{Reg}_{[\tau,\rho]}^q(u)]\le\frac{3(S+1)\log T}{\eta_j}+\eta_j K\mathbb E[H].$$
--   This is the main-learner estimate with the paper's coefficient 3 and stability coefficient 1.
--
--   Differences from the source:
--   - encoding: arms in [K] and finite round sequences → arms in Fin K and natural-indexed functions restricted to rounds 1 through T; reason: relabeling is bijective and values outside the horizon are ignored; NeZero K follows from K ≥ 2
--   - encoding: Algorithm 1 argmin updates and independent Bernoulli and uniform draws → the paper’s normalized exponential closed forms and a finite product of independent uniform coordinates with threshold routing; reason: PDF pp. 20 and 25 derive the closed forms; Appendix A.1 gives this seed law, with unused coordinates integrating out
--   - generalization: the fixed optimal comparator u^(S) → every deterministic arm sequence with at most S switches; reason: the proof uses only the switch bound, and every minimizer is included
--   - generalization: conditional on the start history of a reached epoch → every deterministic j and tau in {1,...,T}, under fresh epoch seeds; reason: the reset state depends only on j and tau and the assigned epoch seeds are independent of the past
--   - encoding: an expectation bound or identity → the same expectation together with explicit integrability of every integrand; reason: makes the source’s finite expectations well-defined rather than relying on total-integral defaults
-- source:
--   Mengxiao Zhang, Toward Optimal Switching Regret for Multi-Armed Bandits with Oblivious Adversary, 2026 preprint, STOC 2027 submission #99, SHA-256 70dc03d632eeb5878823d984fc755157b34301d8189bbd7a6087570a8f8a7fee, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/99.pdf, Lemma 4.1, PDF p. 11 (printed p. 10).

import Definitions.Def_SwitchingRegret_Dyadic_Continuation

open MeasureTheory

namespace SwitchingRegret.Dyadic

theorem lemma_4_1
    {K T : ℕ} [NeZero K] (hK : 2 ≤ K) (hT : K < T)
    (ell : LossTable K) (hell : validLoss T ell)
    (S : ℕ) (hS : S < T) (u : ℕ → Fin K) (hu : switches T u ≤ S)
    (j tau : ℕ) (hj : j ∈ Finset.Icc 1 T) (htau : tau ∈ Finset.Icc 1 T) :
    Integrable (stoppedRegret ell u j tau) (epochLaw T) ∧
    Integrable (stoppedLength ell j tau) (epochLaw T) ∧
      (∫ xi, stoppedRegret ell u j tau xi ∂epochLaw T) ≤
        3 * (S + 1 : ℕ) * Real.log T / eta K T j +
          eta K T j * K * ∫ xi, stoppedLength ell j tau xi ∂epochLaw T := by sorry

end SwitchingRegret.Dyadic
