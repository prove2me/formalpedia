-- Prove2me | Theorems.Thm_WiesemannRMDP_AffineSDP_eq20c_iff_22c
-- name    : WiesemannRMDP.AffineSDP.eq20c_iff_22c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:41:19.89912+00:00
-- url     : https://prove2.me/theorems/e7fa9216-f319-46b5-afe0-260d8edb608d
-- title:
--   Proof of Theorem 3.8 — constraint (20c) at s implies (22c) at s, and for L = 1 the two are equivalent
-- statement:
--   Consider the robust MDP with affine ambiguity set under its standing assumptions, a policy $\pi\in\Pi$, coefficients $w\in\mathbb R^S$, $W\in\mathbb R^{S\times q}$ and a state $s\in\mathcal S$.
--
--   1. If there are multipliers $\Gamma\in\mathbb R^{S\times L}_+$ such that the linear matrix inequality (20c) holds at $s$, then the semi-infinite constraint
--   $$w_s + W_{s\cdot}^\top\xi \le \sum_{a\in\mathcal A}\pi(a\mid s)\,(k_{sa}+K_{sa}\xi)^\top\big(r_{sa}+\lambda[w+W\xi]\big)\qquad\forall\,\xi\in\Xi \tag{22c}$$
--   holds at $s$.
--   2. If $L=1$, the converse holds as well: (22c) at $s$ implies the existence of $\Gamma\in\mathbb R^{S\times 1}_+$ for which (20c) holds at $s$.
--
--   Constraint (22c), over all $s$, is the feasibility constraint of the affine approximate policy evaluation problem (21) with $\widehat P$ and $\widehat r$ written out. This result is why (20) is exact for one quadratic constraint and conservative for several.
--
--   **Formalization Note.** Only the row $\Gamma_{s\cdot}$ enters (20c) at $s$. $\succeq 0$ is nonnegativity of the quadratic form; the matrix of (20c) has the non-symmetric lower-right block $\lambda\sum_a\pi(a\mid s)K_{sa}^\top W$, and only its symmetric part matters.
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), p. 22, proof of Theorem 3.8 ((22c), (20c))

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
Optimization Online 2610, revision of February 9, 2012, p. 22): for every state `s`, constraint (22c) at `s` is
implied by constraint (20c) at `s` (for some row `Γ_{s·} ∈ ℝ^L_+` of multipliers); moreover, if
`L = 1`, both constraints are equivalent. Here `w`, `W` are arbitrary and `π ∈ Π` is fixed.

**Formalization Note.** (20c) at `s` with multipliers `Γ` is `IsPSDForm (lhs20c π s w W Γ)`;
only the row `Γ s` enters it, and the existential is over the whole `Γ ∈ ℝ^{S×L}_+`. The
lower-right block `λ K_saᵀ W` is not symmetric, so `⪰ 0` is the quadratic-form reading. -/
theorem eq20c_iff_22c {St Act : Type*} [Fintype St] [DecidableEq St] [Fintype Act]
    [Nonempty St] [Nonempty Act] {q L : ℕ} (M : Model St Act q L) (hM : M.Standing)
    (π : St → Act → ℝ) (hπ : IsPolicy π) (w : St → ℝ) (W : Matrix St (Fin q) ℝ) (s : St) :
    ((∃ Γ : St → Fin L → ℝ, (∀ s' l, 0 ≤ Γ s' l) ∧ IsPSDForm (M.lhs20c π s w W Γ)) →
        M.Con22c π s w W) ∧
      (L = 1 → M.Con22c π s w W →
        ∃ Γ : St → Fin L → ℝ, (∀ s' l, 0 ≤ Γ s' l) ∧
          IsPSDForm (M.lhs20c π s w W Γ)) := by sorry

end WiesemannRMDP.AffineSDP
