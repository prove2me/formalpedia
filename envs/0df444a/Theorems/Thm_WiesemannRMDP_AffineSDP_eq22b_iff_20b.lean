-- Prove2me | Theorems.Thm_WiesemannRMDP_AffineSDP_eq22b_iff_20b
-- name    : WiesemannRMDP.AffineSDP.eq22b_iff_20b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:41:07.612781+00:00
-- url     : https://prove2.me/theorems/25e615e2-5cb2-49e3-a7b3-fe728e227f8c
-- title:
--   Proof of Theorem 3.8 — constraint (22b) is equivalent to the linear matrix inequality (20b)
-- statement:
--   Consider the robust MDP with affine ambiguity set under its standing assumptions. For every $\tau\in\mathbb R$, $w\in\mathbb R^S$ and $W\in\mathbb R^{S\times q}$, the semi-infinite constraint
--   $$\tau\le p_0^\top(w+W\xi)\qquad\forall\,\xi\in\Xi \tag{22b}$$
--   holds if and only if there is $\gamma\in\mathbb R^L_+$ with
--   $$\begin{bmatrix}p_0^\top w-\tau & \tfrac12 p_0^\top W\\ \tfrac12 W^\top p_0 & 0\end{bmatrix} - \sum_{l=1}^L\gamma_l\begin{bmatrix}\omega_l & \tfrac12 o_l^\top\\ \tfrac12 o_l & O_l\end{bmatrix}\succeq 0. \tag{20b}$$
--
--   This is the exact reformulation of the objective's epigraph constraint in the semidefinite program (20), valid for every number $L$ of constraints defining $\Xi$.
--
--   **Formalization Note.** $\succeq 0$ is nonnegativity of the quadratic form.
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), p. 22, proof of Theorem 3.8 ((22b), (20b))

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
Optimization Online 2610, revision of February 9, 2012, p. 22): constraint (22b), `τ ≤ p₀ᵀ(w + W ξ)` for all
`ξ ∈ Ξ`, is equivalent to constraint (20b): there is `γ ∈ ℝ^L_+` with
`[p₀ᵀw − τ, ½p₀ᵀW; ½Wᵀp₀, 0] − ∑_l γ_l [ω_l, ½o_lᵀ; ½o_l, O_l] ⪰ 0`
(Proposition 3.7 under condition (C2)). Here `τ`, `w`, `W` are arbitrary.

**Formalization Note.** `⪰ 0` is `IsPSDForm`. -/
theorem eq22b_iff_20b {St Act : Type*} [Fintype St] [DecidableEq St] [Fintype Act]
    [Nonempty St] [Nonempty Act] {q L : ℕ} (M : Model St Act q L) (hM : M.Standing)
    (τ : ℝ) (w : St → ℝ) (W : Matrix St (Fin q) ℝ) :
    M.Con22b τ w W ↔
      ∃ γ : Fin L → ℝ, (∀ l, 0 ≤ γ l) ∧
        IsPSDForm (M.lhs20b τ w W - ∑ l : Fin L, γ l • Qblock M.O M.o M.ω l) := by sorry

end WiesemannRMDP.AffineSDP
