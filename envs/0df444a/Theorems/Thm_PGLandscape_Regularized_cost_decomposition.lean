-- Prove2me | Theorems.Thm_PGLandscape_Regularized_cost_decomposition
-- name    : PGLandscape.Regularized.cost_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:27:26.408318+00:00
-- url     : https://prove2.me/theorems/9e7a98d9-9c3a-4c7c-b2d9-7e93d9c87d33
-- title:
--   (34), p. 43 — ℓ_λ(π) = Σ_s η_π(s) g_λ(s, π(s)) = ℓ_0(π) + λ Σ_s η_π(s) D(U‖π(s))
-- statement:
--   In the regularized finite MDP of Example 4, fix $\lambda\ge0$ and a policy $\pi$, i.e. a choice of probability vector $\pi(s)\in\Delta_{k-1}$ at every state. Let $\eta_\pi$ be the discounted state-occupancy distribution of $\pi$ started from $\rho$, $\ell_\lambda$ the regularized and $\ell_0$ the unregularized discounted average cost. Then, as elements of $[0,\infty]$,
--
--   $$
--   \ell_\lambda(\pi)=\sum_{s\in\mathcal S}\eta_\pi(s)\,g_\lambda(s,\pi(s))=\ell_0(\pi)+\lambda\sum_{s\in\mathcal S}\eta_\pi(s)\,D(U\|\pi(s)).
--   $$
--
--   The decomposition separates the regularized objective into the unregularized cost and an occupancy-weighted divergence penalty; it is Step 1 of the proof of Lemma 10.
--
--   **Formalization Note** Both sides live in $[0,\infty]$; a state with $\eta_\pi(s)=0$ contributes $0$ even if $D(U\|\pi(s))=\infty$ ($0\cdot\infty=0$), as on the page.
-- source:
--   arXiv:1906.01786v3, App. E.2, proof of Lemma 10, Step 1, (34), p. 43

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction
import Definitions.Def_PGLandscape_Regularized_Model
open FoundationsML.ReinforcementLearning
open scoped ENNReal

namespace PGLandscape.Regularized

/-- (34), Step 1, p. 43: `ℓ_λ(π) = Σ_s η_π(s) g_λ(s, π(s)) = ℓ_0(π) + λ Σ_s η_π(s) D(U‖π(s))`. -/
theorem cost_decomposition {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]
    (P : S → I → S → ℝ) (gs : S → I → ℝ) (γ : ℝ) (ρ : S → ℝ) (lam : ℝ)
    (hM : IsRegMDP P gs γ ρ) (hlam : 0 ≤ lam) (π : S → I → ℝ) (hπ : IsPolicy π) :
    regLoss P gs γ ρ lam π = ∑ s, ENNReal.ofReal (occFin P γ ρ π s) * regCost gs lam (π s) s ∧
      regLoss P gs γ ρ lam π = ENNReal.ofReal (loss0 P gs γ ρ π) +
        ENNReal.ofReal lam * ∑ s, ENNReal.ofReal (occFin P γ ρ π s) * klUniform (π s) := by sorry

end PGLandscape.Regularized
