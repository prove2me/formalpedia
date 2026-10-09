-- Prove2me | Theorems.Thm_WiesemannRMDP_AffineSDP_feasible_le_rbar
-- name    : WiesemannRMDP.AffineSDP.feasible_le_rbar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:41:09.656363+00:00
-- url     : https://prove2.me/theorems/3de453ca-903d-4c47-8c45-e2ae375b62c7
-- title:
--   Proof of Theorem 3.8 — every feasible affine reward to-go satisfies w + Wξ ≤ r̄e/(1 − λ) on Ξ
-- statement:
--   Consider the robust MDP with affine ambiguity set under its standing assumptions and a fixed policy $\pi\in\Pi$, and let $\bar r := \max_{s,a,s'} r(s,a,s')$. If $(w,W)$ is feasible in the affine approximate policy evaluation problem (21), that is, $w+W\xi\le\widehat r(\xi)+\lambda\widehat P(\xi)(w+W\xi)$ for all $\xi\in\Xi$, then
--   $$w + W\xi \le \frac{\bar r}{1-\lambda}\,e\qquad\forall\,\xi\in\Xi,$$
--   where $e$ is the all-ones vector and the inequality is componentwise.
--
--   This uniform upper bound is one half of the argument that the feasible region of (21) can be taken bounded, which makes (21) solvable.
--
--   **Formalization Note.** $\bar r$ is the supremum of $r$ over the finite set $\mathcal S\times\mathcal A\times\mathcal S$.
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), p. 22, proof of Theorem 3.8

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward
import Definitions.Def_WiesemannRMDP_AffineSDP_ParamSet
import Definitions.Def_WiesemannRMDP_AffineSDP_Model
import Definitions.Def_WiesemannRMDP_AffineSDP_Programs

namespace WiesemannRMDP.AffineSDP

open FoundationsML.ReinforcementLearning Matrix

/-- Proof of Theorem 3.8 (Wiesemann, Kuhn & Rustem, *Robust Markov Decision Processes*,
Optimization Online 2610, revision of February 9, 2012, p. 22): with
`r̄ := max_{s,a,s'} r(s, a, s')`, any feasible solution `(w, W)` of (21) satisfies
`w + W ξ ≤ r̄ e / (1 − λ)` for all `ξ ∈ Ξ`, where `e` is the all-ones vector.

**Formalization Note.** The inequality is componentwise on `ℝ^S`; `r̄ e / (1 − λ)` is the
constant vector `fun _ => r̄ / (1 − λ)`. -/
theorem feasible_le_rbar {St Act : Type*} [Fintype St] [DecidableEq St] [Fintype Act]
    [Nonempty St] [Nonempty Act] {q L : ℕ} (M : Model St Act q L) (hM : M.Standing)
    (π : St → Act → ℝ) (hπ : IsPolicy π) (w : St → ℝ) (W : Matrix St (Fin q) ℝ)
    (hfeas : M.Feas19 π w W) :
    ∀ ξ ∈ M.Xi, w + W *ᵥ ξ ≤ fun _ => M.rbar / (1 - M.lam) := by sorry

end WiesemannRMDP.AffineSDP
