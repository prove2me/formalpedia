-- Prove2me | Theorems.Thm_SensitivityPoA_Holder_lemma_11_b
-- name    : SensitivityPoA.Holder.lemma_11_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:17.089278+00:00
-- url     : https://prove2.me/theorems/adba858f-f858-4ad6-b29b-9470f79eecca
-- title:
--   Lemma 11b), p. 31 — on a cost slice the SO cost is Lipschitz at a game with Lipschitz costs
-- statement:
--   Let $\Gamma_1 = (\pi, w)$ be a game of the game space whose cost functions are Lipschitz continuous on $[0, T(w)]$ with a Lipschitz constant $M \ge 1$, and let $\Gamma_2 = (\pi, w')$ be a game of the game space with the same cost functions and $T(w') \le T(w)$. Put $D = \|\Gamma_1-\Gamma_2\|$, $\pi_{\max}(T(w)) = \max_{a}\pi_a(T(w))$ and
--   $$\nu^*_{\Gamma_1} = 2\big(|A|\,|\mathcal K|\,\pi_{\max}(T(w)) + |A|\,T(w)\,M\,|\mathcal K|\big).$$
--   If $D < T(w)/|\mathcal K|$, then
--   $$|\mathcal C^*(\Gamma_1) - \mathcal C^*(\Gamma_2)| \le \nu^*_{\Gamma_1}\,D.$$
--
--   This is the cost-slice estimate for the optimal cost used in the proof of Theorem 9.
--
--   **Formalization Note** The paper prints $\nu^*_{\Gamma_1} = 2(|A|\,|\mathcal K|\,\pi_{\max}(T(w)) + |A|\,T(w)\,M)$. Its step (4.20) uses $\|\Gamma_1' - \hat\Gamma\| \le M\|\Gamma_1-\Gamma_2\|$, while the shift $\lambda_a$ it rests on is only bounded by $|\mathcal K|\,\|\Gamma_1-\Gamma_2\|$ (p. 33). The statement carries the resulting factor $|\mathcal K|$ on the second term; the two coincide when $|\mathcal K| = 1$.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), pp. 30–31, Lemma 11b)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Holder_Setting

namespace SensitivityPoA.Holder
open KellyStochasticNetworks

/-- Lemma 11b), p. 31, with the factor `|K|` the proof needs on the second term of `ν∗`
(printed: `ν∗ = 2·(|A|·|K|·π_max(T(w)) + |A|·T(w)·M)`). -/
theorem lemma_11_b (N : Network) (hN : N.Standing) (Γ1 Γ2 : Game N)
    (h1 : Γ1 ∈ gameSpace N) (h2 : Γ2 ∈ gameSpace N) (hτ : Γ2.τ = Γ1.τ)
    (hT : totalDemand Γ2.d ≤ totalDemand Γ1.d)
    (M : ℝ) (hM1 : 1 ≤ M) (hM : ∀ j, LipOnIcc (Γ1.τ j) (totalDemand Γ1.d) M) :
    let T : ℝ := totalDemand Γ1.d
    let D : ℝ := gameDist Γ1 Γ2
    let πmax : ℝ := ⨆ j, Γ1.τ j T
    let νtil : ℝ := 2 * ((Real.sqrt (M * N.J * T) + 2) * N.J * T + N.J * N.Sd * πmax) * Real.sqrt M
    let νstar : ℝ := 2 * (N.J * N.Sd * πmax + N.J * T * M * N.Sd)
    let X : ℝ := max (Real.sqrt (N.Sd * D)) (Real.sqrt M * (N.Sd * D))
    D < T / N.Sd → |SOCost Γ1 - SOCost Γ2| ≤ νstar * D := by sorry

end SensitivityPoA.Holder
