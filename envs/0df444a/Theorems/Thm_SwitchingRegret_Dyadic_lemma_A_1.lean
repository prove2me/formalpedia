-- Prove2me | Theorems.Thm_SwitchingRegret_Dyadic_lemma_A_1
-- name    : SwitchingRegret.Dyadic.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:27:40.236198+00:00
-- url     : https://prove2.me/theorems/4b6086d9-c1c9-4f67-8405-85bceae783fb
-- title:
--   Lemma A.1 — completed-simplex OMD bound
-- statement:
--   Let $T>K\ge2$, fix a bounded deterministic loss table, and take any fresh continuation with $j,\tau\in[1,T]$. Fix every seed in $(0,1)$, a canonical interval $J$ starting at or after $\tau$, and any endpoint $n\in[1,T]$. For every $v\in X$, including boundary points, let $\bar v$ denote its completion and $\pi$ the completed initial distribution. On challenge rounds set $y_{t,J,0}=\langle q_t,\widehat\ell_{t,J}\rangle$ and $y_{t,J,i}=\widehat\ell_{t,J,i}$. Then
--   $$\sum_{t\in J,\ t\le n,\ b_t=0}\langle x_{t,J}-v,z_{t,J}\rangle\le\frac{\operatorname{KL}(\bar v\Vert\pi)}{\eta_J}+\frac{\eta_J}{2}\sum_{t\in J,\ t\le n,\ b_t=0}\langle\bar x_{t,J},y_{t,J}^2\rangle.$$
--   This is a pathwise statement on the full sub-simplex, with zero coordinates contributing zero to relative entropy.
--
--   Differences from the source:
--   - encoding: arms in [K] and finite round sequences → arms in Fin K and natural-indexed functions restricted to rounds 1 through T; reason: relabeling is bijective and values outside the horizon are ignored; NeZero K follows from K ≥ 2
--   - encoding: Algorithm 1 argmin updates and independent Bernoulli and uniform draws → the paper’s normalized exponential closed forms and a finite product of independent uniform coordinates with threshold routing; reason: PDF pp. 20 and 25 derive the closed forms; Appendix A.1 gives this seed law, with unused coordinates integrating out
--   - generalization: conditional on the start history of a reached epoch → every deterministic j and tau in {1,...,T}, under fresh epoch seeds; reason: the reset state depends only on j and tau and the assigned epoch seeds are independent of the past
--   - encoding: pathwise interval bound on the supported draws → every seed coordinate lies in (0,1); reason: the uniform seed space has this support and positivity excludes the undefined inverse-rate input U_J = 0
-- source:
--   Mengxiao Zhang, Toward Optimal Switching Regret for Multi-Armed Bandits with Oblivious Adversary, 2026 preprint, STOC 2027 submission #99, SHA-256 70dc03d632eeb5878823d984fc755157b34301d8189bbd7a6087570a8f8a7fee, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/99.pdf, Lemma A.1, PDF p. 25 (printed p. 24).

import Definitions.Def_SwitchingRegret_Dyadic_Continuation

open MeasureTheory

namespace SwitchingRegret.Dyadic

theorem lemma_A_1
    {K T : ℕ} [NeZero K] (hK : 2 ≤ K) (hT : K < T)
    (ell : LossTable K) (hell : validLoss T ell)
    (j tau : ℕ) (hj : j ∈ Finset.Icc 1 T) (htau : tau ∈ Finset.Icc 1 T)
    (xi : EpochSeed T) (hxi : ∀ a, xi a ∈ Set.Ioo (0 : ℝ) 1)
    (J : Dyad T) (hJ : J ∈ future T tau) (n : ℕ) (hn : n ∈ Finset.Icc 1 T)
    (u : Vec K) (hu : subSimplex u) :
    omdRegret ell j tau xi J n u ≤ finiteKL (complete u) (prior K T) / intervalRate K T j xi J +
      intervalRate K T j xi J / 2 * omdSecondOrder ell j tau xi J n := by sorry

end SwitchingRegret.Dyadic
