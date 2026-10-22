-- Prove2me | Theorems.Thm_SensitivityPoA_Holder_lemma_1_c
-- name    : SensitivityPoA.Holder.lemma_1_c
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:15.317415+00:00
-- url     : https://prove2.me/theorems/793b84d0-03c6-4d2b-b730-9bb9c790b569
-- title:
--   Lemma 1c), p. 13 — with M-Lipschitz costs, an ǫ-approximate WE flow costs within |A|·√(M·ǫ)·T(d) + ǫ of a WE flow
-- statement:
--   Let $\Gamma = (\tau, d)$ be a generalized nonatomic congestion game, $\epsilon > 0$, $f$ an $\epsilon$-approximate WE flow and $\tilde f$ a WE flow of $\Gamma$. Suppose every arc cost $\tau_a$ is Lipschitz continuous on $[0, T(d)]$ with Lipschitz constant $M > 0$. Write $L_k(\tau,d) = \min_{s'\in\mathcal S_k}\tau_{s'}(\tilde f)$ for the user cost of pair $k$ (2.2). Then:
--   1. $|\tau_a(f_a) - \tau_a(\tilde f_a)| \le \sqrt{M\epsilon}$ for every arc $a$;
--   2. $|L_k(\tau,d) - \min_{s'\in\mathcal S_k}\tau_{s'}(f)| \le |A|\sqrt{M\epsilon}$ for every O/D pair $k$;
--   3. $$|C(\Gamma, f) - C(\Gamma, \tilde f)| \le |A|\sqrt{M\epsilon}\,T(d) + \epsilon.$$
--
--   This is the estimate that produces the exponent $1/2$ in the Hölder continuity of the price of anarchy (Lemma 10d), Theorem 9); Example 2 shows it is tight.
--
--   **Formalization Note** `Network.Basic` contains G1–G2 but does not impose the later Condition 1. The first bound is printed with "$<$"; Example 2 ($M = 1$) gives $|\tau_u(f_u) - \tau_u(\tilde f_u)| = \sqrt\epsilon$, as the paper notes on p. 14, so the statement uses $\le$. $|A|$ is the number of arcs, cast to a real number.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 13, Lemma 1c)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Holder_Setting

namespace SensitivityPoA.Holder
open KellyStochasticNetworks

/-- Lemma 1c), p. 13 (the first printed `<` read `≤`, attained in Example 2). The user cost
`L_k(τ, d)` (2.2) is `minPathCost Γ ftil k` for the WE flow `ftil`. -/
theorem lemma_1_c (N : Network) (hN : N.Basic) (Γ : Game N) (hΓ : Γ.IsGeneralized)
    (ε : ℝ) (hε : 0 < ε) (f ftil : Fin N.R → ℝ) (hf : IsApproxWE Γ ε f) (hftil : IsWE Γ ftil)
    (M : ℝ) (hM0 : 0 < M) (hM : ∀ j, LipOnIcc (Γ.τ j) (totalDemand Γ.d) M) :
    (∀ j, |Γ.τ j (linkFlow N.A f j) - Γ.τ j (linkFlow N.A ftil j)| ≤ Real.sqrt (M * ε)) ∧
    (∀ k, |minPathCost Γ ftil k - minPathCost Γ f k| ≤ (N.J : ℝ) * Real.sqrt (M * ε)) ∧
    |cost Γ f - cost Γ ftil| ≤ (N.J : ℝ) * Real.sqrt (M * ε) * totalDemand Γ.d + ε := by sorry

end SensitivityPoA.Holder
