-- Prove2me | Theorems.Thm_SwitchingRegret_Dyadic_lemma_4_2
-- name    : SwitchingRegret.Dyadic.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:27:37.182786+00:00
-- url     : https://prove2.me/theorems/f1eb2088-864e-4d79-9c97-8c2398e5cbca
-- title:
--   Lemma 4.2 — both small-rate epoch bounds
-- statement:
--   Let $T>K\ge2$, let $\ell\in[0,1]^{T\times K}$ be deterministic before any seed is drawn, and let $u$ be a deterministic arm sequence with at most $S<T$ switches. For any deterministic $j,\tau\in\{1,\ldots,T\}$, run the fresh rate-$\eta_j$ continuation from round $\tau$. Let $\rho$ be its first threshold crossing, or $T$, with the crossing round included. There is one absolute constant $C>0$, chosen before $K,T,\ell,S,u,j,\tau$, for which both random variables below are integrable and
--   $$\mathbb E\!\left[\sum_{J\in D_j(\rho)}A_J(\rho)\right]\le C\left(\eta_jKT L^2+\sqrt{(S+1)KT}\,L^3\right),$$
--   $$\mathbb E[\operatorname{Reg}_{[\tau,\rho]}^q(u)]\le C\left(\eta_jKT L^2+\sqrt{(S+1)KT}\,L^3\right).$$
--   The cover and each advantage are evaluated at the same random endpoint $\rho$. This item retains both Eqs (15) and (16).
--
--   Differences from the source:
--   - encoding: arms in [K] and finite round sequences → arms in Fin K and natural-indexed functions restricted to rounds 1 through T; reason: relabeling is bijective and values outside the horizon are ignored; NeZero K follows from K ≥ 2
--   - encoding: Algorithm 1 argmin updates and independent Bernoulli and uniform draws → the paper’s normalized exponential closed forms and a finite product of independent uniform coordinates with threshold routing; reason: PDF pp. 20 and 25 derive the closed forms; Appendix A.1 gives this seed law, with unused coordinates integrating out
--   - generalization: the fixed optimal comparator u^(S) → every deterministic arm sequence with at most S switches; reason: the proof uses only the switch bound, and every minimizer is included
--   - generalization: conditional on the start history of a reached epoch → every deterministic j and tau in {1,...,T}, under fresh epoch seeds; reason: the reset state depends only on j and tau and the assigned epoch seeds are independent of the past
--   - encoding: an expectation bound or identity → the same expectation together with explicit integrability of every integrand; reason: makes the source’s finite expectations well-defined rather than relying on total-integral defaults
--   - encoding: two bounds written with O notation → one positive absolute constant bounding both displays; reason: the maximum of two positive absolute constants gives the same pair of O bounds
-- source:
--   Mengxiao Zhang, Toward Optimal Switching Regret for Multi-Armed Bandits with Oblivious Adversary, 2026 preprint, STOC 2027 submission #99, SHA-256 70dc03d632eeb5878823d984fc755157b34301d8189bbd7a6087570a8f8a7fee, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/99.pdf, Lemma 4.2, PDF p. 12 (printed p. 11).

import Definitions.Def_SwitchingRegret_Dyadic_Continuation

open MeasureTheory

namespace SwitchingRegret.Dyadic

theorem lemma_4_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (K T : ℕ) [NeZero K], 2 ≤ K → K < T →
      ∀ (ell : LossTable K), validLoss T ell →
      ∀ (S : ℕ), S < T → ∀ (u : ℕ → Fin K), switches T u ≤ S →
      ∀ (j tau : ℕ), j ∈ Finset.Icc 1 T → tau ∈ Finset.Icc 1 T →
      let B := C * (eta K T j * K * T * (L T : ℝ) ^ 2 +
        Real.sqrt (((S + 1 : ℕ) : ℝ) * K * T) * (L T : ℝ) ^ 3)
      Integrable (stoppedAdvantage ell u j tau) (epochLaw T) ∧
      Integrable (stoppedRegret ell u j tau) (epochLaw T) ∧
        (∫ xi, stoppedAdvantage ell u j tau xi ∂epochLaw T) ≤ B ∧
        (∫ xi, stoppedRegret ell u j tau xi ∂epochLaw T) ≤ B := by sorry

end SwitchingRegret.Dyadic
