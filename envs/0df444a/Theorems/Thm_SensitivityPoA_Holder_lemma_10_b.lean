-- Prove2me | Theorems.Thm_SensitivityPoA_Holder_lemma_10_b
-- name    : SensitivityPoA.Holder.lemma_10_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:12.621976+00:00
-- url     : https://prove2.me/theorems/4af4245a-04d5-4a71-b9bc-0534c34bbc23
-- title:
--   Lemma 10b), p. 27 — on a demand slice the potential values of WE flows differ by O(|A|·T(w)·‖Γ1 − Γ2‖)
-- statement:
--   Let $\Gamma_1 = (\pi^{(1)}, w)$ and $\Gamma_2 = (\pi^{(2)}, w)$ be two games of the game space with the same demand vector $w$, and let $\tilde f$ and $\tilde g$ be WE flows of $\Gamma_1$ and $\Gamma_2$. Then
--   1. $|\Phi(\Gamma_1, f) - \Phi(\Gamma_2, f)| \le |A|\,T(w)\,\|\Gamma_1-\Gamma_2\|$ for every flow $f$;
--   2. $|\Phi(\Gamma_1, \tilde f) - \Phi(\Gamma_2, \tilde g)| \le |A|\,T(w)\,\|\Gamma_1-\Gamma_2\|$;
--   3. $0 \le \Phi(\Gamma_1, \tilde g) - \Phi(\Gamma_1, \tilde f) \le 2|A|\,T(w)\,\|\Gamma_1-\Gamma_2\|$;
--   4. $0 \le \Phi(\Gamma_2, \tilde f) - \Phi(\Gamma_2, \tilde g) \le 2|A|\,T(w)\,\|\Gamma_1-\Gamma_2\|$.
--
--   The WE flow of each game is thus an almost-minimizer of the other game's potential.
--
--   **Formalization Note** "Every flow" is a flow of the common demand vector $w$.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 27, Lemma 10b)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Holder_Setting

namespace SensitivityPoA.Holder
open KellyStochasticNetworks

/-- Lemma 10b), p. 27: potential values on a demand slice. -/
theorem lemma_10_b (N : Network) (hN : N.Standing) (Γ1 Γ2 : Game N)
    (h1 : Γ1 ∈ gameSpace N) (h2 : Γ2 ∈ gameSpace N) (hd : Γ1.d = Γ2.d)
    (ftil gtil : Fin N.R → ℝ) (hftil : IsWE Γ1 ftil) (hgtil : IsWE Γ2 gtil) :
    (∀ f, IsFlow Γ1 f →
      |potential Γ1 f - potential Γ2 f| ≤ (N.J : ℝ) * totalDemand Γ1.d * gameDist Γ1 Γ2) ∧
    |potential Γ1 ftil - potential Γ2 gtil| ≤ (N.J : ℝ) * totalDemand Γ1.d * gameDist Γ1 Γ2 ∧
    (0 ≤ potential Γ1 gtil - potential Γ1 ftil ∧
      potential Γ1 gtil - potential Γ1 ftil ≤ 2 * (N.J : ℝ) * totalDemand Γ1.d * gameDist Γ1 Γ2) ∧
    (0 ≤ potential Γ2 ftil - potential Γ2 gtil ∧
      potential Γ2 ftil - potential Γ2 gtil ≤ 2 * (N.J : ℝ) * totalDemand Γ1.d * gameDist Γ1 Γ2) := by sorry

end SensitivityPoA.Holder
