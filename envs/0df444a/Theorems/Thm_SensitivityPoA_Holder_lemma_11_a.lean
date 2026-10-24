-- Prove2me | Theorems.Thm_SensitivityPoA_Holder_lemma_11_a
-- name    : SensitivityPoA.Holder.lemma_11_a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:15.435698+00:00
-- url     : https://prove2.me/theorems/7c307063-e82d-4655-94c9-8413e711c02c
-- title:
--   Lemma 11a), p. 31 — on a cost slice the WE cost is Hölder with exponent 1/2 at a game with Lipschitz costs
-- statement:
--   Let $\Gamma_1 = (\pi, w)$ be a game of the game space whose cost functions $\pi_a$ are Lipschitz continuous on $[0, T(w)]$ with a Lipschitz constant $M \ge 1$, and let $\Gamma_2 = (\pi, w')$ be a game of the game space with the same cost functions and $T(w') \le T(w)$. Put $D = \|\Gamma_1 - \Gamma_2\|$, $\pi_{\max}(T(w)) = \max_{a\in A}\pi_a(T(w))$ and
--   $$\tilde\nu_{\Gamma_1} = 2\Big(\big(\sqrt{M\,|A|\,T(w)} + 2\big)|A|\,T(w) + |A|\,|\mathcal K|\,\pi_{\max}(T(w))\Big)\sqrt M.$$
--   If $D < T(w)/|\mathcal K|$, then
--   $$|\tilde{\mathcal C}(\Gamma_2) - \tilde{\mathcal C}(\Gamma_1)| \le \tilde\nu_{\Gamma_1}\max\Big\{\sqrt{|\mathcal K|\,D},\ \sqrt M\,|\mathcal K|\,D\Big\}.$$
--
--   This is the cost-slice estimate for the WE cost used in the proof of Theorem 9.
--
--   **Formalization Note** The paper prints the maximum as $\max\{\sqrt D, \sqrt M\,D\}$. Its proof bounds $\|\Gamma_1' - \hat\Gamma\|$ by $M\max_a\mu_a \le M\|w - w'\|_\infty$ (p. 32), but $\mu_a = \sum_{s\ni a}\mu_s$ can be as large as $|\mathcal K|\,\|w-w'\|_\infty$ (the proof of 11b) uses exactly this bound, p. 33). With the correct bound $M|\mathcal K|D$ the argument proves the statement above; the two coincide when $|\mathcal K| = 1$. $\tilde\nu_{\Gamma_1}$ is as printed. $\pi_{\max}$ is a supremum over the finite arc set.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), pp. 30–31, Lemma 11a)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Holder_Setting

namespace SensitivityPoA.Holder
open KellyStochasticNetworks

/-- Lemma 11a), p. 31, with the factor `|K|` the proof needs inside the maximum (printed:
`max{√‖Γ1 − Γ2‖, √M·‖Γ1 − Γ2‖}`); `ν̃_{Γ1}` as printed. -/
theorem lemma_11_a (N : Network) (hN : N.Standing) (Γ1 Γ2 : Game N)
    (h1 : Γ1 ∈ gameSpace N) (h2 : Γ2 ∈ gameSpace N) (hτ : Γ2.τ = Γ1.τ)
    (hT : totalDemand Γ2.d ≤ totalDemand Γ1.d)
    (M : ℝ) (hM1 : 1 ≤ M) (hM : ∀ j, LipOnIcc (Γ1.τ j) (totalDemand Γ1.d) M) :
    let T : ℝ := totalDemand Γ1.d
    let D : ℝ := gameDist Γ1 Γ2
    let πmax : ℝ := ⨆ j, Γ1.τ j T
    let νtil : ℝ := 2 * ((Real.sqrt (M * N.J * T) + 2) * N.J * T + N.J * N.Sd * πmax) * Real.sqrt M
    let νstar : ℝ := 2 * (N.J * N.Sd * πmax + N.J * T * M * N.Sd)
    let X : ℝ := max (Real.sqrt (N.Sd * D)) (Real.sqrt M * (N.Sd * D))
    D < T / N.Sd → |WECost Γ2 - WECost Γ1| ≤ νtil * X := by sorry

end SensitivityPoA.Holder
