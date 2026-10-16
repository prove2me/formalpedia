-- Prove2me | Theorems.Thm_SensitivityPoA_Holder_lemma_10_d
-- name    : SensitivityPoA.Holder.lemma_10_d
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:31.40603+00:00
-- url     : https://prove2.me/theorems/a71791cc-6f90-436a-86fc-67e893f012af
-- title:
--   Lemma 10d), p. 27 — on a demand slice, C̃ and ρ are Hölder with exponent 1/2 at a game with M-Lipschitz costs
-- statement:
--   Let $\Gamma_1 = (\pi^{(1)}, w)$ and $\Gamma_2 = (\pi^{(2)}, w)$ be two games of the game space with the same demand vector $w$, and suppose every $\pi^{(1)}_a$ is Lipschitz continuous on $[0, T(w)]$ with Lipschitz constant $M > 0$. Write $D = \|\Gamma_1 - \Gamma_2\|$. Then
--   $$|\tilde{\mathcal C}(\Gamma_1) - \tilde{\mathcal C}(\Gamma_2)| \le \big(\sqrt{M\,|A|\,T(w)} + 2\big)\,|A|\,T(w)\,\max\{\sqrt D, D\},$$
--   and, when $D \le \mathcal C^*(\Gamma_1)/(2|A|\,T(w))$,
--   $$|\rho(\Gamma_1) - \rho(\Gamma_2)| \le \nu_{\Gamma_1}\max\{\sqrt D, D\},\qquad \nu_{\Gamma_1} = 2\cdot\frac{\rho(\Gamma_1) + \sqrt{M\,|A|\,T(w)} + 2}{\mathcal C^*(\Gamma_1)}\cdot|A|\,T(w).$$
--
--   This is the demand-slice half of Theorem 9.
--
--   **Formalization Note** The distance condition is attached to the bound on $\rho$ only; the bound on $\tilde{\mathcal C}$ holds for every pair of games of the slice (the paper's proof, (4.11)).
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 27, Lemma 10d)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Holder_Setting

namespace SensitivityPoA.Holder
open KellyStochasticNetworks

/-- Lemma 10d), p. 27: Hölder bounds of exponent 1/2 for `C̃` and `ρ` on a demand slice. -/
theorem lemma_10_d (N : Network) (hN : N.Standing) (Γ1 Γ2 : Game N)
    (h1 : Γ1 ∈ gameSpace N) (h2 : Γ2 ∈ gameSpace N) (hd : Γ1.d = Γ2.d)
    (M : ℝ) (hM0 : 0 < M) (hM : ∀ j, LipOnIcc (Γ1.τ j) (totalDemand Γ1.d) M) :
    |WECost Γ1 - WECost Γ2|
        ≤ (Real.sqrt (M * N.J * totalDemand Γ1.d) + 2) * N.J * totalDemand Γ1.d
          * max (Real.sqrt (gameDist Γ1 Γ2)) (gameDist Γ1 Γ2) ∧
    (gameDist Γ1 Γ2 ≤ SOCost Γ1 / (2 * N.J * totalDemand Γ1.d) →
      |PoA Γ1 - PoA Γ2|
        ≤ 2 * (PoA Γ1 + Real.sqrt (M * N.J * totalDemand Γ1.d) + 2) / SOCost Γ1
            * (N.J * totalDemand Γ1.d)
          * max (Real.sqrt (gameDist Γ1 Γ2)) (gameDist Γ1 Γ2)) := by sorry

end SensitivityPoA.Holder
