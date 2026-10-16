-- Prove2me | Theorems.Thm_SensitivityPoA_Holder_lemma_10_c
-- name    : SensitivityPoA.Holder.lemma_10_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:31.067989+00:00
-- url     : https://prove2.me/theorems/022dff8d-28a1-4731-a815-5820f2ade074
-- title:
--   Lemma 10c), p. 27 — WE flows of two games of a demand slice are mutually |A|·T(w)·‖Γ1 − Γ2‖-approximate WE flows
-- statement:
--   Let $\Gamma_1 = (\pi^{(1)}, w)$ and $\Gamma_2 = (\pi^{(2)}, w)$ be two games of the game space with the same demand vector $w$, and let $\tilde f$ and $\tilde g$ be WE flows of $\Gamma_1$ and $\Gamma_2$. Then $\tilde f$ is an $\epsilon$-approximate WE flow of $\Gamma_2$ and $\tilde g$ is an $\epsilon$-approximate WE flow of $\Gamma_1$, with
--   $$\epsilon = |A|\cdot T(w)\cdot\|\Gamma_1 - \Gamma_2\|.$$
--
--   Combined with Lemma 1c) this gives the Hölder estimate of Lemma 10d).
--
--   **Formalization Note** (2.7) is stated for a small constant $\epsilon > 0$; the formal notion of $\epsilon$-approximate WE takes any real $\epsilon$, and here $\epsilon = 0$ when $\Gamma_1$ and $\Gamma_2$ coincide on $[0, T(w)]$.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 27, Lemma 10c)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Holder_Setting

namespace SensitivityPoA.Holder
open KellyStochasticNetworks

/-- Lemma 10c), p. 27: WE flows of two games of a demand slice are mutually
`|A|·T(w)·‖Γ1 − Γ2‖`-approximate WE flows. -/
theorem lemma_10_c (N : Network) (hN : N.Standing) (Γ1 Γ2 : Game N)
    (h1 : Γ1 ∈ gameSpace N) (h2 : Γ2 ∈ gameSpace N) (hd : Γ1.d = Γ2.d)
    (ftil gtil : Fin N.R → ℝ) (hftil : IsWE Γ1 ftil) (hgtil : IsWE Γ2 gtil) :
    IsApproxWE Γ2 ((N.J : ℝ) * totalDemand Γ1.d * gameDist Γ1 Γ2) ftil ∧
    IsApproxWE Γ1 ((N.J : ℝ) * totalDemand Γ1.d * gameDist Γ1 Γ2) gtil := by sorry

end SensitivityPoA.Holder
