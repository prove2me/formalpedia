-- Prove2me | Theorems.Thm_WiesemannRMDP_AffineSDP_eq21_solvable
-- name    : WiesemannRMDP.AffineSDP.eq21_solvable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:41:00.362039+00:00
-- url     : https://prove2.me/theorems/41f05aac-7c22-4d3c-af13-d4875853bafe
-- title:
--   Proof of Theorem 3.8 — the affine approximate policy evaluation problem (21) is solvable
-- statement:
--   Consider the robust MDP with affine ambiguity set under its standing assumptions and a fixed policy $\pi\in\Pi$. The problem
--   $$\sup_{w\in\mathbb R^S,\ W\in\mathbb R^{S\times q}}\Big\{\inf_{\xi\in\Xi}p_0^\top(w+W\xi) \;:\; w+W\xi\le\widehat r(\xi)+\lambda\widehat P(\xi)(w+W\xi)\ \ \forall\,\xi\in\Xi\Big\} \tag{21}$$
--   is solvable: there is a feasible $(w^\star,W^\star)$ whose objective value $\inf_{\xi\in\Xi}p_0^\top(w^\star+W^\star\xi)$ is at least the objective value of every feasible $(w,W)$.
--
--   In particular the supremum of (19) is a maximum, which is what part (a) of Theorem 3.8 compares with the optimal value of the semidefinite program (20).
--
--   **Formalization Note.** Solvability is the existence of a feasible point whose value is the greatest element of the set of objective values of feasible points.
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), pp. 21–22, proof of Theorem 3.8

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
Optimization Online 2610, revision of February 9, 2012, pp. 21–22): problem (21) — equivalently the affine
approximate policy evaluation problem (19) — is solvable: some feasible `(w, W)` attains the
supremum of the objective `inf_{ξ∈Ξ} p₀ᵀ(w + W ξ)` over all feasible solutions.

**Formalization Note.** Solvability is stated as: some feasible `(w, W)` has objective value
`val19 w W` that is the greatest element of the set of objective values of feasible
solutions. -/
theorem eq21_solvable {St Act : Type*} [Fintype St] [DecidableEq St] [Fintype Act]
    [Nonempty St] [Nonempty Act] {q L : ℕ} (M : Model St Act q L) (hM : M.Standing)
    (π : St → Act → ℝ) (hπ : IsPolicy π) :
    ∃ (w : St → ℝ) (W : Matrix St (Fin q) ℝ),
      M.Feas19 π w W ∧ IsGreatest (M.values19 π) (M.val19 w W) := by sorry

end WiesemannRMDP.AffineSDP
