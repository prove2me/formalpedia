-- Prove2me | Theorems.Thm_SensitivityPoA_Continuity_lemma_5_b
-- name    : SensitivityPoA.Continuity.lemma_5_b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:04.201917+00:00
-- url     : https://prove2.me/theorems/f5ca00f7-f091-42cc-8ae0-89b85bb6c626
-- title:
--   Lemma 5b, p. 18 — limits of social optima and optimum costs
-- statement:
--   Let $\Gamma_n\to\Gamma$ be games in the game space, and choose a social-optimum flow $f_n^*$ of each $\Gamma_n$. If a subsequence indexed by a strictly increasing sequence of natural numbers converges to a nonnegative vector $f^*$, then $f^*$ is a social optimum of $\Gamma$. If $\Gamma$ has a unique social optimum, the whole sequence $f_n^*$ converges to it. In particular,
--   $$C^*(\Gamma_n)\longrightarrow C^*(\Gamma).$$
--   The final conclusion gives continuity of the optimum-cost map even when optimum flows are not unique.
--
--   **Formalization Note** A strictly increasing index map represents the paper's infinite subsequence. The limit vector's nonnegativity is stated as on the page. Uniqueness is a premise only of the conditional whole-flow convergence clause.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 18, Lemma 5b)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Continuity_Setting

namespace SensitivityPoA.Continuity

theorem lemma_5_b (N : Network) (hN : N.Standing)
    (Γ : Game N) (hΓ : Γ ∈ gameSpace N)
    (Γs : ℕ → Game N) (hΓs : ∀ n, Γs n ∈ gameSpace N)
    (hlim : Filter.Tendsto (fun n => gameDist (Γs n) Γ) Filter.atTop (nhds 0))
    (fs : ℕ → Fin N.R → ℝ) (hfs : ∀ n, IsSO (Γs n) (fs n))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (fstar : Fin N.R → ℝ) (hfstar : ∀ r, 0 ≤ fstar r)
    (hsub : Filter.Tendsto (fun i => fs (φ i)) Filter.atTop (nhds fstar)) :
    IsSO Γ fstar ∧
    ((∃! g : Fin N.R → ℝ, IsSO Γ g) →
      ∃ g : Fin N.R → ℝ, IsSO Γ g ∧ Filter.Tendsto fs Filter.atTop (nhds g)) ∧
    Filter.Tendsto (fun n => SOCost (Γs n)) Filter.atTop (nhds (SOCost Γ)) := by sorry

end SensitivityPoA.Continuity
