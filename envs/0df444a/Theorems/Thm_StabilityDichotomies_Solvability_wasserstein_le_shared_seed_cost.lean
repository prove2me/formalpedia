-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_wasserstein_le_shared_seed_cost
-- name    : StabilityDichotomies.Solvability.wasserstein_le_shared_seed_cost
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:07:18.259101+00:00
-- url     : https://prove2.me/theorems/11ce612a-7d74-4d5d-9733-cbcc48851a8f
-- title:
--   Shared randomness bounds Wasserstein distance
-- statement:
--   Let $\mu$ be a probability law on a finite random-seed space, and let $f$ and $g$ be two Boolean assignment-valued outputs computed from the same seed. The Wasserstein distance between their output laws is at most the expected Hamming distance $\mathbb E_{\omega\sim\mu}d_H(f(\omega),g(\omega))$. This gives the coupling bound needed when comparing an algorithm before and after deleting a constraint.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.3, p.17.

import Definitions.Def_StabilityDichotomies_Solvability_Stability
noncomputable section
open scoped Classical BigOperators ENNReal

namespace StabilityDichotomies.Solvability
theorem wasserstein_le_shared_seed_cost {V Ω : Type} [Fintype V] [Fintype Ω]
    (μ : PMF Ω) (f g : Ω → V → Bool) :
    wasserstein (μ.map f) (μ.map g) ≤
      ∑ ω, (μ ω).toReal * hammingCost (f ω) (g ω) := by sorry
end StabilityDichotomies.Solvability
