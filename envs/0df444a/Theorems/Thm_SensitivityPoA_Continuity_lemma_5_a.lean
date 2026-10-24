-- Prove2me | Theorems.Thm_SensitivityPoA_Continuity_lemma_5_a
-- name    : SensitivityPoA.Continuity.lemma_5_a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T17:38:57.779531+00:00
-- url     : https://prove2.me/theorems/4d8ae932-b137-44bf-90e9-ca033f94ad1d
-- title:
--   Lemma 5a, p. 18 — approximate a limiting feasible flow
-- statement:
--   Suppose games $\Gamma_n$ in the game space converge to another game $\Gamma$ in the distance of (3.3). For any feasible flow $f$ of $\Gamma$, there are feasible flows $f^{(n)}$ of the respective games $\Gamma_n$ such that
--   $$f^{(n)}\longrightarrow f.$$
--   This lets flow comparisons at the limit game be approximated along a varying-demand sequence.
--
--   **Formalization Note** Flow convergence is in the finite product topology. The source's construction of the approximating flows overlooks pairs with zero limiting demand; the statement remains valid for those pairs.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 18, Lemma 5a)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Continuity_Setting

namespace SensitivityPoA.Continuity

theorem lemma_5_a (N : Network) (hN : N.Standing)
    (Γ : Game N) (hΓ : Γ ∈ gameSpace N)
    (Γs : ℕ → Game N) (hΓs : ∀ n, Γs n ∈ gameSpace N)
    (hlim : Filter.Tendsto (fun n => gameDist (Γs n) Γ) Filter.atTop (nhds 0))
    (f : Fin N.R → ℝ) (hf : IsFlow Γ f) :
    ∃ fs : ℕ → Fin N.R → ℝ,
      (∀ n, IsFlow (Γs n) (fs n)) ∧ Filter.Tendsto fs Filter.atTop (nhds f) := by sorry

end SensitivityPoA.Continuity
