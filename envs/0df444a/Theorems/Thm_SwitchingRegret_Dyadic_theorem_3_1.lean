-- Prove2me | Theorems.Thm_SwitchingRegret_Dyadic_theorem_3_1
-- name    : SwitchingRegret.Dyadic.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:27:51.827575+00:00
-- url     : https://prove2.me/theorems/6afdcb14-a1e8-4400-baac-1fe09010ee1f
-- title:
--   Theorem 3.1 — simultaneous expected switching regret
-- statement:
--   Let $T>K\ge2$, let $\ell\in[0,1]^{T\times K}$ be deterministic before any seed is drawn, and let $u$ be a deterministic arm sequence with at most $S<T$ switches. For Algorithm 1, which takes only $K,T$ and sees only the selected arm's loss, there is an absolute $C>0$, chosen before every instance parameter, such that
--   $$\mathbb E[\operatorname{Reg}_T(u)]\le C\sqrt{(S+1)KT}\,(\log T)^4.$$
--   The regret is $\sum_{t=1}^T(\langle p_t,\ell_t\rangle-\ell_{t,u_t})$, using the actual sampling distribution, and its seed-to-regret map is measurable and integrable. The same algorithm and the same constant serve every $S\in\{0,\ldots,T-1\}$; the algorithm receives neither $S$ nor $u$. All logarithms are natural and the fourth power lies outside the square root.
--
--   This specializes to the source's best switching comparator under any deterministic tie rule.
--
--   Differences from the source:
--   - encoding: arms in [K] and finite round sequences → arms in Fin K and natural-indexed functions restricted to rounds 1 through T; reason: relabeling is bijective and values outside the horizon are ignored; NeZero K follows from K ≥ 2
--   - encoding: Algorithm 1 argmin updates and independent Bernoulli and uniform draws → the paper’s normalized exponential closed forms and a finite product of independent uniform coordinates with threshold routing; reason: PDF pp. 20 and 25 derive the closed forms; Appendix A.1 gives this seed law, with unused coordinates integrating out
--   - generalization: the fixed optimal comparator u^(S) → every deterministic arm sequence with at most S switches; reason: the proof uses only the switch bound, and every minimizer is included
--   - encoding: an expectation bound or identity → the same expectation together with measurability and integrability of the regret integrand; reason: makes the source’s finite expectations well-defined rather than relying on total-integral defaults
--   - encoding: O of the stated rate → a positive absolute constant before all parameters; reason: this is the meaning of the source’s O notation; no rate factor is changed
-- source:
--   Mengxiao Zhang, Toward Optimal Switching Regret for Multi-Armed Bandits with Oblivious Adversary, 2026 preprint, STOC 2027 submission #99, SHA-256 70dc03d632eeb5878823d984fc755157b34301d8189bbd7a6087570a8f8a7fee, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/99.pdf, Theorem 3.1, PDF p. 8 (printed p. 7).

import Definitions.Def_SwitchingRegret_Dyadic_Continuation

open MeasureTheory

namespace SwitchingRegret.Dyadic

theorem theorem_3_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (K T : ℕ) [NeZero K], 2 ≤ K → K < T →
      ∀ (ell : LossTable K), validLoss T ell →
      ∀ (S : ℕ), S < T → ∀ (u : ℕ → Fin K), switches T u ≤ S →
      let f := fun omega : RunSeed T => regretOn (run ell omega) ell u (Finset.Icc 1 T) false
      Measurable f ∧ Integrable f (runLaw T) ∧
        (∫ omega, f omega ∂runLaw T) ≤
          C * Real.sqrt (((S + 1 : ℕ) : ℝ) * K * T) * (Real.log T) ^ 4 := by sorry

end SwitchingRegret.Dyadic
