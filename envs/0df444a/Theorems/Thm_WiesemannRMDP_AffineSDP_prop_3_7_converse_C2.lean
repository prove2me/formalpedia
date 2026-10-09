-- Prove2me | Theorems.Thm_WiesemannRMDP_AffineSDP_prop_3_7_converse_C2
-- name    : WiesemannRMDP.AffineSDP.prop_3_7_converse_C2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:41:00.216118+00:00
-- url     : https://prove2.me/theorems/dea4ee0d-3a7f-470d-92f4-0fd9d407a654
-- title:
--   Proposition 3.7, (C2) — for S ⪰ 0 nonnegativity of ξᵀSξ + sᵀξ + σ on Ξ has an S-lemma certificate
-- statement:
--   Let $\Xi=\{\xi\in\mathbb R^q:\xi^\top O_l\xi+o_l^\top\xi+\omega_l\ge 0,\ l=1,\dots,L\}$ be a parameter set of the form (3b) satisfying the standing assumptions ($O_l\preceq 0$, $\Xi$ bounded, Slater point). Let $S\in\mathbb S^q$ with $S\succeq 0$, $s\in\mathbb R^q$ and $\sigma\in\mathbb R$. If
--   $$\xi^\top S\xi + s^\top\xi + \sigma \ge 0\qquad\forall\,\xi\in\Xi,$$
--   then there is $\gamma\in\mathbb R^L_+$ with
--   $$\begin{bmatrix}\sigma & \tfrac12 s^\top\\ \tfrac12 s & S\end{bmatrix} - \sum_{l=1}^L\gamma_l\begin{bmatrix}\omega_l & \tfrac12 o_l^\top\\ \tfrac12 o_l & O_l\end{bmatrix}\succeq 0.$$
--
--   This is the reversed implication of (17) under condition (C2) of Proposition 3.7, for any number $L$ of constraints. Applied with $S=0$ it shows that constraint (22b) and the linear matrix inequality (20b) are equivalent.
--
--   **Formalization Note.** $S\succeq 0$ is Mathlib's positive semidefiniteness (which includes symmetry); the conclusion uses the quadratic-form reading of $\succeq 0$. The case (C1) $L=1$ of the reversed implication is the published S-procedure, referenced in this mission.
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), p. 20, Proposition 3.7, reversed implication under (C2)

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

/-- Proposition 3.7, reversed implication under condition (C2) (Wiesemann, Kuhn & Rustem, *Robust Markov Decision Processes*,
Optimization Online 2610, revision of February 9, 2012, p. 20): for `Ξ`
defined in (3b) and any fixed `S ∈ 𝕊^q` with `S ⪰ 0`, `s ∈ ℝ^q` and `σ ∈ ℝ`, if
`ξᵀ S ξ + sᵀ ξ + σ ≥ 0` for all `ξ ∈ Ξ`, then there is `γ ∈ ℝ^L_+` with
`[σ, ½sᵀ; ½s, S] − ∑_l γ_l [ω_l, ½o_lᵀ; ½o_l, O_l] ⪰ 0`.

**Formalization Note.** The data of (3b) carry the paper's standing assumptions (`XiStanding`:
`O_l ⪯ 0`, `Ξ` bounded, Slater point). `S ⪰ 0` is Mathlib's `PosSemidef` (which includes
symmetry, `S ∈ 𝕊^q`). The matrix inequality in the conclusion is `IsPSDForm`. -/
theorem prop_3_7_converse_C2 {q L : ℕ} (O : Fin L → Matrix (Fin q) (Fin q) ℝ)
    (o : Fin L → Fin q → ℝ) (ω : Fin L → ℝ) (hΞ : XiStanding O o ω)
    (Smat : Matrix (Fin q) (Fin q) ℝ) (hS : Smat.PosSemidef) (s : Fin q → ℝ) (σ : ℝ) :
    (∀ ξ ∈ XiSet O o ω, 0 ≤ ξ ⬝ᵥ (Smat *ᵥ ξ) + s ⬝ᵥ ξ + σ) →
      ∃ γ : Fin L → ℝ, (∀ l, 0 ≤ γ l) ∧
        IsPSDForm (quadBlock σ s Smat - ∑ l : Fin L, γ l • Qblock O o ω l) := by sorry

end WiesemannRMDP.AffineSDP
