-- Prove2me | Theorems.Thm_WiesemannRMDP_AffineSDP_prop_3_7_eq17
-- name    : WiesemannRMDP.AffineSDP.prop_3_7_eq17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:41:07.589007+00:00
-- url     : https://prove2.me/theorems/46163958-e192-4b5e-b1d4-301aed513042
-- title:
--   Proposition 3.7, implication (17) — an S-lemma certificate γ ≥ 0 implies ξᵀSξ + sᵀξ + σ ≥ 0 on Ξ
-- statement:
--   Let $\Xi=\{\xi\in\mathbb R^q:\xi^\top O_l\xi+o_l^\top\xi+\omega_l\ge 0,\ l=1,\dots,L\}$ be a parameter set of the form (3b) satisfying the standing assumptions ($O_l\preceq 0$, $\Xi$ bounded, Slater point). Let $S\in\mathbb S^q$ be symmetric, $s\in\mathbb R^q$ and $\sigma\in\mathbb R$. If there is $\gamma\in\mathbb R^L_+$ with
--   $$\begin{bmatrix}\sigma & \tfrac12 s^\top\\ \tfrac12 s & S\end{bmatrix} - \sum_{l=1}^L\gamma_l\begin{bmatrix}\omega_l & \tfrac12 o_l^\top\\ \tfrac12 o_l & O_l\end{bmatrix}\succeq 0,$$
--   then
--   $$\xi^\top S\xi + s^\top\xi + \sigma \ge 0\qquad\forall\,\xi\in\Xi. \tag{17}$$
--
--   This is the approximate S-lemma: a linear matrix inequality in $\gamma$ certifies that a quadratic function is nonnegative on $\Xi$. It is what makes the semidefinite program (20) a conservative approximation of the semi-infinite constraints (22b)–(22c).
--
--   **Formalization Note.** The standing assumptions on $\Xi$ are hypotheses because the paper states the proposition for $\Xi$ as defined in (3b) under them; this implication does not use them. $\succeq 0$ is nonnegativity of the quadratic form, which for this symmetric block matrix is positive semidefiniteness.
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), p. 20, Proposition 3.7, implication (17)

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

/-- Proposition 3.7, implication (17) (Wiesemann, Kuhn & Rustem, *Robust Markov Decision Processes*,
Optimization Online 2610, revision of February 9, 2012, p. 20): for `Ξ` defined in (3b) and any fixed
`S ∈ 𝕊^q`, `s ∈ ℝ^q` and `σ ∈ ℝ`,
`∃ γ ∈ ℝ^L_+ : [σ, ½sᵀ; ½s, S] − ∑_l γ_l [ω_l, ½o_lᵀ; ½o_l, O_l] ⪰ 0` implies
`ξᵀ S ξ + sᵀ ξ + σ ≥ 0` for all `ξ ∈ Ξ`.

**Formalization Note.** The data of (3b) carry the paper's standing assumptions (`XiStanding`:
`O_l ⪯ 0`, `Ξ` bounded, Slater point), although this implication does not use them. `S` is
named `Smat` and is symmetric (`𝕊^q`). `⪰ 0` is `IsPSDForm` (nonnegative quadratic form),
which for this symmetric block matrix is positive semidefiniteness. -/
theorem prop_3_7_eq17 {q L : ℕ} (O : Fin L → Matrix (Fin q) (Fin q) ℝ) (o : Fin L → Fin q → ℝ)
    (ω : Fin L → ℝ) (hΞ : XiStanding O o ω) (Smat : Matrix (Fin q) (Fin q) ℝ)
    (hS : Smat.IsSymm) (s : Fin q → ℝ) (σ : ℝ) :
    (∃ γ : Fin L → ℝ, (∀ l, 0 ≤ γ l) ∧
        IsPSDForm (quadBlock σ s Smat - ∑ l : Fin L, γ l • Qblock O o ω l)) →
      ∀ ξ ∈ XiSet O o ω, 0 ≤ ξ ⬝ᵥ (Smat *ᵥ ξ) + s ⬝ᵥ ξ + σ := by sorry

end WiesemannRMDP.AffineSDP
