-- Prove2me | Theorems.Thm_SensitivityPoA_Holder_lemma_1_b
-- name    : SensitivityPoA.Holder.lemma_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:23.869477+00:00
-- url     : https://prove2.me/theorems/d179423a-4c40-4b72-9ce2-dac4a561f776
-- title:
--   Lemma 1b), p. 13 — potential gap between an ǫ-approximate WE flow and a WE flow
-- statement:
--   Let $\Gamma = (\tau, d)$ be a generalized nonatomic congestion game, $\epsilon > 0$, $f$ an $\epsilon$-approximate WE flow and $\tilde f$ a WE flow of $\Gamma$, with arc flows $f_a$ and $\tilde f_a$. Then
--   $$0 \le \sum_{a\in A}\tau_a(\tilde f_a)(f_a - \tilde f_a) \le \Phi(\Gamma, f) - \Phi(\Gamma, \tilde f) \le \sum_{a\in A}\tau_a(f_a)(f_a - \tilde f_a) \le \epsilon,$$
--   and consequently
--   $$0 \le \sum_{a\in A}|\tau_a(f_a) - \tau_a(\tilde f_a)|\cdot|f_a - \tilde f_a| \le \epsilon.$$
--
--   The second estimate is what turns approximate equilibrium into closeness of arc costs in Lemma 1c).
--
--   **Formalization Note** `Network.Basic` contains G1–G2 but does not impose the later Condition 1. Both upper bounds are printed as "$< \epsilon$"; Example 2 attains equality in both, so the statement uses $\le$.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 13, Lemma 1b)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Holder_Setting

namespace SensitivityPoA.Holder
open KellyStochasticNetworks

/-- Lemma 1b), p. 13 (both printed `< ǫ` read `≤ ǫ`, attained in Example 2). -/
theorem lemma_1_b (N : Network) (hN : N.Basic) (Γ : Game N) (hΓ : Γ.IsGeneralized)
    (ε : ℝ) (hε : 0 < ε) (f ftil : Fin N.R → ℝ) (hf : IsApproxWE Γ ε f) (hftil : IsWE Γ ftil) :
    (0 ≤ ∑ j, Γ.τ j (linkFlow N.A ftil j) * (linkFlow N.A f j - linkFlow N.A ftil j) ∧
      ∑ j, Γ.τ j (linkFlow N.A ftil j) * (linkFlow N.A f j - linkFlow N.A ftil j)
        ≤ potential Γ f - potential Γ ftil ∧
      potential Γ f - potential Γ ftil
        ≤ ∑ j, Γ.τ j (linkFlow N.A f j) * (linkFlow N.A f j - linkFlow N.A ftil j) ∧
      ∑ j, Γ.τ j (linkFlow N.A f j) * (linkFlow N.A f j - linkFlow N.A ftil j) ≤ ε) ∧
    (0 ≤ ∑ j, |Γ.τ j (linkFlow N.A f j) - Γ.τ j (linkFlow N.A ftil j)|
          * |linkFlow N.A f j - linkFlow N.A ftil j| ∧
      ∑ j, |Γ.τ j (linkFlow N.A f j) - Γ.τ j (linkFlow N.A ftil j)|
          * |linkFlow N.A f j - linkFlow N.A ftil j| ≤ ε) := by sorry

end SensitivityPoA.Holder
