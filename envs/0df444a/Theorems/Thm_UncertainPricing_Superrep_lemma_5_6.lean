-- Prove2me | Theorems.Thm_UncertainPricing_Superrep_lemma_5_6
-- name    : UncertainPricing.Superrep.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:38.518031+00:00
-- url     : https://prove2.me/theorems/8122ea4c-2e07-45d3-82ec-9a73bb9c0aff
-- title:
--   Lemma 5.6, p. 22 — f = G(S), S = sup_{t∈[0,T]} B_t, is in Γ for bounded continuous G
-- statement:
--   Let $\mathbf P$ be a set of martingale measures on $\Omega$ satisfying $H(\bar\mu)$, with $\bar\mu$ Hölder continuous. Let $S=\sup_{t\in[0,T]}B_t$ and let $G:\mathbb R\to\mathbb R$ be bounded continuous. Then
--   $$f=G(S)\in\Gamma .$$
--
--   This covers lookback-type claims on the running maximum.
--
--   **Formalization Note.** $S(\omega)$ is a real supremum over the compact interval $[0,T]$ of a continuous path, hence attained and finite. Membership in $\Gamma$ means $E_Q\tilde f=E_{Q^*}f$ for every $Q\in\mathcal Q$.
-- source:
--   Denis & Martini, arXiv:math/0607111v1, Lemma 5.6 and the definition of S before it, p. 22

import Mathlib
import Definitions.Def_UncertainPricing_Superrep_Setting
import Definitions.Def_UncertainPricing_Superrep_Compact

namespace UncertainPricing.Superrep

open MeasureTheory Filter Topology BoundedContinuousFunction

theorem lemma_5_6 (T : ℝ) (hT : 0 < T) (μU : StieltjesFunction ℝ) (hμU : IsDistFn T μU)
    (Ps : Set (Measure (Ω T))) (hPs : ∀ P ∈ Ps, IsMartingaleMeasure P ∧ HypU μU P)
    (hHol : IsHolder T μU) (f : Ω T →ᵇ ℝ) (hf : IsSupClaim f) : InGamma Ps μU f := by sorry

end UncertainPricing.Superrep
