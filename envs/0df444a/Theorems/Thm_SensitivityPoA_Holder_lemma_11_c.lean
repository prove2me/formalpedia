-- Prove2me | Theorems.Thm_SensitivityPoA_Holder_lemma_11_c
-- name    : SensitivityPoA.Holder.lemma_11_c
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:20.564709+00:00
-- url     : https://prove2.me/theorems/6892f3ec-3e86-406d-8fce-58431b4da3da
-- title:
--   Lemma 11c), p. 31 — on a cost slice the PoA is Hölder with exponent 1/2 at a game with Lipschitz costs
-- statement:
--   Let $\Gamma_1 = (\pi, w)$ and $\Gamma_2 = (\pi, w')$ be as in Lemma 11a)–b): both in the game space, same cost functions, $T(w') \le T(w)$, and the $\pi_a$ Lipschitz on $[0,T(w)]$ with constant $M \ge 1$. With $D$, $\tilde\nu_{\Gamma_1}$ and $\nu^*_{\Gamma_1}$ as in Lemma 11a)–b), put
--   $$\nu'_{\Gamma_1} = \frac{2\rho(\Gamma_1)\,\nu^*_{\Gamma_1} + 2\tilde\nu_{\Gamma_1}}{\mathcal C^*(\Gamma_1)}.$$
--   If $D < T(w)/|\mathcal K|$ and $D \le \mathcal C^*(\Gamma_1)/(2\nu^*_{\Gamma_1})$, then
--   $$|\rho(\Gamma_1) - \rho(\Gamma_2)| \le \nu'_{\Gamma_1}\max\Big\{\sqrt{|\mathcal K|\,D},\ \sqrt M\,|\mathcal K|\,D\Big\}.$$
--
--   This is the cost-slice half of Theorem 9.
--
--   **Formalization Note** Four readings differ from the print. (i) $\nu^*$ and the maximum carry the factor $|\mathcal K|$ of Lemma 11a)–b) (see there). (ii) The print defines $\nu'$ with $\tilde\nu_{\Gamma_2}$; the proof uses $\tilde\nu_{\Gamma_1}$. (iii) The print has a strict "$<$", which fails at $\Gamma_2 = \Gamma_1$; the statement uses $\le$. (iv) The print requires $D \le \min\{T(w)/|\mathcal K|, \mathcal C^*(\Gamma_1)/(2\nu^*_{\Gamma_1})\}$; parts a)–b), which c) uses, need $D < T(w)/|\mathcal K|$, so the first entry is strict.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), pp. 30–31, Lemma 11c)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Holder_Setting

namespace SensitivityPoA.Holder
open KellyStochasticNetworks

/-- Lemma 11c), p. 31, with the corrected `ν∗`, `ν̃_{Γ1}` (printed `ν̃_{Γ2}`), the factor `|K|` in the
maximum, `≤` (printed `<`) and `‖Γ1 − Γ2‖ < T(w)/|K|` (printed `≤`). -/
theorem lemma_11_c (N : Network) (hN : N.Standing) (Γ1 Γ2 : Game N)
    (h1 : Γ1 ∈ gameSpace N) (h2 : Γ2 ∈ gameSpace N) (hτ : Γ2.τ = Γ1.τ)
    (hT : totalDemand Γ2.d ≤ totalDemand Γ1.d)
    (M : ℝ) (hM1 : 1 ≤ M) (hM : ∀ j, LipOnIcc (Γ1.τ j) (totalDemand Γ1.d) M) :
    let T : ℝ := totalDemand Γ1.d
    let D : ℝ := gameDist Γ1 Γ2
    let πmax : ℝ := ⨆ j, Γ1.τ j T
    let νtil : ℝ := 2 * ((Real.sqrt (M * N.J * T) + 2) * N.J * T + N.J * N.Sd * πmax) * Real.sqrt M
    let νstar : ℝ := 2 * (N.J * N.Sd * πmax + N.J * T * M * N.Sd)
    let X : ℝ := max (Real.sqrt (N.Sd * D)) (Real.sqrt M * (N.Sd * D))
    let νprime : ℝ := (2 * PoA Γ1 * νstar + 2 * νtil) / SOCost Γ1
    D < T / N.Sd → D ≤ SOCost Γ1 / (2 * νstar) → |PoA Γ1 - PoA Γ2| ≤ νprime * X := by sorry

end SensitivityPoA.Holder
