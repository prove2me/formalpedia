-- Prove2me | Theorems.Thm_SwitchingRegret_Dyadic_lemma_4_8
-- name    : SwitchingRegret.Dyadic.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:28:17.527625+00:00
-- url     : https://prove2.me/theorems/54be6cf9-ff22-4454-a63b-2fca3cd05bbb
-- title:
--   Lemma 4.8 — credit pays for stability
-- statement:
--   Let $T>K\ge2$ and fix an oblivious loss table in $[0,1]^{T\times K}$. For Algorithm 1's actual run, let $N$ be the number of reached epochs, $H_j$ their lengths and $C_j$ their final credits. The difference inside the expectation is integrable and satisfies
--   $$\mathbb E\!\left[\sum_{j=1}^N\eta_jKH_j-\sum_{j=1}^N C_j\right]\le2KT\eta_1.$$
--   This compares all reached epochs, including the last epoch when no threshold is reached.
--
--   Differences from the source:
--   - encoding: arms in [K] and finite round sequences → arms in Fin K and natural-indexed functions restricted to rounds 1 through T; reason: relabeling is bijective and values outside the horizon are ignored; NeZero K follows from K ≥ 2
--   - encoding: Algorithm 1 argmin updates and independent Bernoulli and uniform draws → the paper’s normalized exponential closed forms and a finite product of independent uniform coordinates with threshold routing; reason: PDF pp. 20 and 25 derive the closed forms; Appendix A.1 gives this seed law, with unused coordinates integrating out
--   - encoding: an expectation bound or identity → the same expectation together with explicit integrability of every integrand; reason: makes the source’s finite expectations well-defined rather than relying on total-integral defaults
-- source:
--   Mengxiao Zhang, Toward Optimal Switching Regret for Multi-Armed Bandits with Oblivious Adversary, 2026 preprint, STOC 2027 submission #99, SHA-256 70dc03d632eeb5878823d984fc755157b34301d8189bbd7a6087570a8f8a7fee, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/99.pdf, Lemma 4.8, PDF p. 15 (printed p. 14).

import Definitions.Def_SwitchingRegret_Dyadic_Continuation

open MeasureTheory

namespace SwitchingRegret.Dyadic

theorem lemma_4_8
    {K T : ℕ} [NeZero K] (hK : 2 ≤ K) (hT : K < T)
    (ell : LossTable K) (hell : validLoss T ell) :
    Integrable (fun omega : RunSeed T => stabilityMinusCredit (run ell omega) ell) (runLaw T) ∧
      (∫ omega, stabilityMinusCredit (run ell omega) ell ∂runLaw T) ≤ 2 * K * T * eta K T 1 := by sorry

end SwitchingRegret.Dyadic
