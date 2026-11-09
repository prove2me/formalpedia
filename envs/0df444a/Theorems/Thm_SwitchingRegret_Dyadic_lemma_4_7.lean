-- Prove2me | Theorems.Thm_SwitchingRegret_Dyadic_lemma_4_7
-- name    : SwitchingRegret.Dyadic.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:28:29.090834+00:00
-- url     : https://prove2.me/theorems/e3d52bc0-68ba-4ad0-9014-92358fb54424
-- title:
--   Lemma 4.7 — expected maximum negative credit
-- statement:
--   Let $T>K\ge2$, fix an oblivious table in $[0,1]^{T\times K}$ and any $j,\tau\in[1,T]$. In its fresh fixed-rate continuation let
--   $$F_j=\max_{\tau\le n\le T}(-C^{\rm cont}_{j,n})_+.$$
--   Then $F_j$ is integrable and
--   $$\mathbb E[F_j]\le KT\eta_j.$$
--   This controls the entire continuation's maximum negative credit, rather than just its value at the stopped endpoint.
--
--   Differences from the source:
--   - encoding: arms in [K] and finite round sequences → arms in Fin K and natural-indexed functions restricted to rounds 1 through T; reason: relabeling is bijective and values outside the horizon are ignored; NeZero K follows from K ≥ 2
--   - encoding: Algorithm 1 argmin updates and independent Bernoulli and uniform draws → the paper’s normalized exponential closed forms and a finite product of independent uniform coordinates with threshold routing; reason: PDF pp. 20 and 25 derive the closed forms; Appendix A.1 gives this seed law, with unused coordinates integrating out
--   - generalization: conditional on the start history of a reached epoch → every deterministic j and tau in {1,...,T}, under fresh epoch seeds; reason: the reset state depends only on j and tau and the assigned epoch seeds are independent of the past
--   - encoding: an expectation bound or identity → the same expectation together with explicit integrability of every integrand; reason: makes the source’s finite expectations well-defined rather than relying on total-integral defaults
-- source:
--   Mengxiao Zhang, Toward Optimal Switching Regret for Multi-Armed Bandits with Oblivious Adversary, 2026 preprint, STOC 2027 submission #99, SHA-256 70dc03d632eeb5878823d984fc755157b34301d8189bbd7a6087570a8f8a7fee, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/99.pdf, Lemma 4.7, PDF p. 15 (printed p. 14).

import Definitions.Def_SwitchingRegret_Dyadic_Continuation

open MeasureTheory

namespace SwitchingRegret.Dyadic

theorem lemma_4_7
    {K T : ℕ} [NeZero K] (hK : 2 ≤ K) (hT : K < T)
    (ell : LossTable K) (hell : validLoss T ell)
    (j tau : ℕ) (hj : j ∈ Finset.Icc 1 T) (htau : tau ∈ Finset.Icc 1 T) :
    Integrable (negativeCredit ell j tau) (epochLaw T) ∧
      (∫ xi, negativeCredit ell j tau xi ∂epochLaw T) ≤ (K : ℝ) * T * eta K T j := by sorry

end SwitchingRegret.Dyadic
