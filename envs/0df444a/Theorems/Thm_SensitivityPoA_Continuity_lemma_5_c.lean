-- Prove2me | Theorems.Thm_SensitivityPoA_Continuity_lemma_5_c
-- name    : SensitivityPoA.Continuity.lemma_5_c
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:02.179229+00:00
-- url     : https://prove2.me/theorems/f11f1a87-5b15-483b-915e-47bf78572e68
-- title:
--   Lemma 5c, p. 19 — limits of Wardrop equilibria and equilibrium costs
-- statement:
--   Let $\Gamma_n\to\Gamma$ be games in the game space, and choose a Wardrop-equilibrium flow $\tilde f_n$ of each $\Gamma_n$. If a subsequence indexed by a strictly increasing sequence of natural numbers converges to a nonnegative vector $\tilde f$, then $\tilde f$ is a Wardrop equilibrium of $\Gamma$. If $\Gamma$ has a unique Wardrop equilibrium, the whole sequence $\tilde f_n$ converges to it. In particular,
--   $$\widetilde C(\Gamma_n)\longrightarrow\widetilde C(\Gamma).$$
--   The equilibrium cost therefore varies continuously even where equilibrium flows are not unique.
--
--   **Formalization Note** The limit vector's nonnegativity is stated as on the page; uniqueness conditions only the whole-flow convergence clause. The equilibrium cost is the supremum of costs over equilibrium flows.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 19, Lemma 5c)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Continuity_Setting

namespace SensitivityPoA.Continuity

theorem lemma_5_c (N : Network) (hN : N.Standing)
    (Γ : Game N) (hΓ : Γ ∈ gameSpace N)
    (Γs : ℕ → Game N) (hΓs : ∀ n, Γs n ∈ gameSpace N)
    (hlim : Filter.Tendsto (fun n => gameDist (Γs n) Γ) Filter.atTop (nhds 0))
    (fs : ℕ → Fin N.R → ℝ) (hfs : ∀ n, IsWE (Γs n) (fs n))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (fwe : Fin N.R → ℝ) (hfwe : ∀ r, 0 ≤ fwe r)
    (hsub : Filter.Tendsto (fun i => fs (φ i)) Filter.atTop (nhds fwe)) :
    IsWE Γ fwe ∧
    ((∃! g : Fin N.R → ℝ, IsWE Γ g) →
      ∃ g : Fin N.R → ℝ, IsWE Γ g ∧ Filter.Tendsto fs Filter.atTop (nhds g)) ∧
    Filter.Tendsto (fun n => WECost (Γs n)) Filter.atTop (nhds (WECost Γ)) := by sorry

end SensitivityPoA.Continuity
