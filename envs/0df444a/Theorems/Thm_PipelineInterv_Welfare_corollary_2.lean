-- Prove2me | Theorems.Thm_PipelineInterv_Welfare_corollary_2
-- name    : PipelineInterv.Welfare.corollary_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:22:59.538583+00:00
-- url     : https://prove2.me/theorems/e167d5ae-acc9-4ff3-b507-8d99f54caf46
-- title:
--   Corollary 2, p. 12 — expected reward is ‖R‖∞-Lipschitz in the ℓ1 distance of the input distribution
-- statement:
--   Let $R\in\mathbb R^w$ be any real vector, let $D,D'\in\mathcal D$ be probability distributions with $\|D-D'\|_1\le\varepsilon$, and let $M\in\mathbb R^{w\times w}$ be left stochastic. Then
--   $$R^\top MD\ \ge\ R^\top MD'-\|R\|_\infty\cdot\varepsilon .$$
--
--   Replacing the true distribution at a layer by a nearby point of the net changes the expected final reward by at most $\|R\|_\infty\varepsilon$, whatever transition (or product of transitions) follows.
--
--   **Formalization Note.** $\|R\|_\infty=\max_i|R_i|$ and $\|\cdot\|_1$ are written out; no sign condition is placed on $R$ or $\varepsilon$, exactly as on the page.
-- source:
--   Arunachaleswaran, Kannan, Roth, Ziani, Pipeline Interventions, arXiv:2002.06592v2, p. 12, Corollary 2

import Mathlib
import Definitions.Def_PipelineInterv_Welfare_Model

namespace PipelineInterv.Welfare
open Matrix

theorem corollary_2 {w : ℕ} (R : Fin w → ℝ) (D D' : Fin w → ℝ) (hD : IsDist D) (hD' : IsDist D')
    (ε : ℝ) (hDD' : l1 (D - D') ≤ ε) (M : Matrix (Fin w) (Fin w) ℝ)
    (hM : M ∈ colStochastic ℝ (Fin w)) :
    R ⬝ᵥ (M *ᵥ D') - supNorm R * ε ≤ R ⬝ᵥ (M *ᵥ D) := by sorry

end PipelineInterv.Welfare
