-- Prove2me | Theorems.Thm_SwitchingRegret_Dyadic_lemma_4_6
-- name    : SwitchingRegret.Dyadic.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:27:44.447315+00:00
-- url     : https://prove2.me/theorems/667fe749-78ce-4584-a330-1faba0fb7b17
-- title:
--   Lemma 4.6 — integrable truncated continuation cost
-- statement:
--   Let $T>K\ge2$ and $j,\tau\in[1,T]$. Give each canonical interval starting at or after $\tau$ its independent rate $\eta_J=\alpha\eta_j/U_J$. For
--   $$\Gamma_j=\sum_{J\in\mathcal J_j}|J|\min\{K\eta_J,\alpha\},$$
--   the random variable $\Gamma_j$ is integrable and
--   $$\mathbb E[\Gamma_j]\le\frac{KT\eta_j}{16}.$$
--   The assertion concerns the truncated sum, although the untruncated rates have infinite expectation. Losses and routing do not enter this sum.
--
--   Differences from the source:
--   - encoding: arms in [K] and finite round sequences → arms in Fin K and natural-indexed functions restricted to rounds 1 through T; reason: relabeling is bijective and values outside the horizon are ignored; NeZero K follows from K ≥ 2
--   - encoding: Algorithm 1 argmin updates and independent Bernoulli and uniform draws → the paper’s normalized exponential closed forms and a finite product of independent uniform coordinates with threshold routing; reason: PDF pp. 20 and 25 derive the closed forms; Appendix A.1 gives this seed law, with unused coordinates integrating out
--   - generalization: conditional on the start history of a reached epoch → every deterministic j and tau in {1,...,T}, under fresh epoch seeds; reason: the reset state depends only on j and tau and the assigned epoch seeds are independent of the past
--   - encoding: an expectation bound or identity → the same expectation together with explicit integrability of every integrand; reason: makes the source’s finite expectations well-defined rather than relying on total-integral defaults
-- source:
--   Mengxiao Zhang, Toward Optimal Switching Regret for Multi-Armed Bandits with Oblivious Adversary, 2026 preprint, STOC 2027 submission #99, SHA-256 70dc03d632eeb5878823d984fc755157b34301d8189bbd7a6087570a8f8a7fee, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/99.pdf, Lemma 4.6, PDF p. 14 (printed p. 13).

import Definitions.Def_SwitchingRegret_Dyadic_Continuation

open MeasureTheory

namespace SwitchingRegret.Dyadic

theorem lemma_4_6 {K T : ℕ} (hK : 2 ≤ K) (hT : K < T)
    (j tau : ℕ) (hj : j ∈ Finset.Icc 1 T) (htau : tau ∈ Finset.Icc 1 T) :
    Integrable (Gamma K T j tau) (epochLaw T) ∧
      (∫ xi, Gamma K T j tau xi ∂epochLaw T) ≤ (K : ℝ) * T * eta K T j / 16 := by sorry

end SwitchingRegret.Dyadic
