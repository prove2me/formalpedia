-- Prove2me | Theorems.Thm_SwitchingRegret_Dyadic_equation_12
-- name    : SwitchingRegret.Dyadic.equation_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:27:40.568658+00:00
-- url     : https://prove2.me/theorems/a1c98038-8476-4238-a500-14bdc18bb0f8
-- title:
--   Epoch decomposition of expected regret
-- statement:
--   Let $T>K\ge2$, let $\ell\in[0,1]^{T\times K}$ be deterministic before any seed is drawn, and let $u$ be a deterministic arm sequence with at most $S<T$ switches. For Algorithm 1's actual run, let $N$ be the number of epochs, $I_j$ their round sets and $C_j=\sum_{t\in I_j}Z_t$ their credits. Both random variables below are integrable, and
--   $$\mathbb E[\operatorname{Reg}_T(u)]=\mathbb E\!\left[\sum_{j=1}^N\operatorname{Reg}_{I_j}^q(u)-\sum_{j=1}^N C_j\right].$$
--   This identity preserves the credit contribution when passing from the main sequence to the distribution actually sampled.
--
--   Differences from the source:
--   - encoding: arms in [K] and finite round sequences → arms in Fin K and natural-indexed functions restricted to rounds 1 through T; reason: relabeling is bijective and values outside the horizon are ignored; NeZero K follows from K ≥ 2
--   - encoding: Algorithm 1 argmin updates and independent Bernoulli and uniform draws → the paper’s normalized exponential closed forms and a finite product of independent uniform coordinates with threshold routing; reason: PDF pp. 20 and 25 derive the closed forms; Appendix A.1 gives this seed law, with unused coordinates integrating out
--   - generalization: the fixed optimal comparator u^(S) → every deterministic arm sequence with at most S switches; reason: the proof uses only the switch bound, and every minimizer is included
--   - encoding: an expectation bound or identity → the same expectation together with explicit integrability of every integrand; reason: makes the source’s finite expectations well-defined rather than relying on total-integral defaults
-- source:
--   Mengxiao Zhang, Toward Optimal Switching Regret for Multi-Armed Bandits with Oblivious Adversary, 2026 preprint, STOC 2027 submission #99, SHA-256 70dc03d632eeb5878823d984fc755157b34301d8189bbd7a6087570a8f8a7fee, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/99.pdf, Section 4, Eq. (12), PDF p. 11 (printed p. 10).

import Definitions.Def_SwitchingRegret_Dyadic_Continuation

open MeasureTheory

namespace SwitchingRegret.Dyadic

theorem equation_12
    {K T : ℕ} [NeZero K] (hK : 2 ≤ K) (hT : K < T)
    (ell : LossTable K) (hell : validLoss T ell)
    (S : ℕ) (hS : S < T) (u : ℕ → Fin K) (hu : switches T u ≤ S) :
    let f := fun omega : RunSeed T => regretOn (run ell omega) ell u (Finset.Icc 1 T) false
    let g := fun omega : RunSeed T => decomposition (run ell omega) ell u
    Integrable f (runLaw T) ∧ Integrable g (runLaw T) ∧
      (∫ omega, f omega ∂runLaw T) = ∫ omega, g omega ∂runLaw T := by sorry

end SwitchingRegret.Dyadic
