-- Prove2me | Theorems.Thm_SmallGainISS_Lyapunov_candidate_5_4
-- name    : SmallGainISS.Lyapunov.candidate_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:10:36.620094+00:00
-- url     : https://prove2.me/theorems/0d53ebf4-31f7-48e5-b66b-e865d86fe3ef
-- title:
--   Theorem 5.3, (5.4): $\max_i\sigma_i^{-1}(V_i(x_i))$ is a Lyapunov function candidate (Assumption 2.1)
-- statement:
--   Let $V_1,\dots,V_n$ ($n\ge1$), $V_i:\mathbb R^{N_i}\to\mathbb R_+$, each satisfy Assumption 2.1: continuous, $\psi_{1}(\|x_i\|)\le V_i(x_i)\le\psi_{2}(\|x_i\|)$ for some $\psi_1,\psi_2\in\mathcal K_\infty$, and locally Lipschitz away from $0$. Let $\sigma_1,\dots,\sigma_n\in\mathcal K_\infty$ have inverses $\sigma_i^{-1}$ that are locally Lipschitz on $(0,\infty)$ (Definition 5.1 (i)). Then
--   $$V(x)=\max_{i=1,\dots,n}\sigma_i^{-1}(V_i(x_i)),\qquad x=(x_1^T,\dots,x_n^T)^T\in\mathbb R^N,$$
--   satisfies Assumption 2.1 on $\mathbb R^N$ (with the Euclidean norm): it is continuous, proper and positive definite, and locally Lipschitz on $\mathbb R^N\setminus\{0\}$.
--
--   This is the "Lyapunov function candidate" half of Theorem 5.3: the function (5.4) belongs to the class in which Definition 2.2 is posed.
--
--   **Formalization Note** Only the parts of the Ω-path definition that this claim uses (the components are $\mathcal K_\infty$, the inverses are locally Lipschitz on $(0,\infty)$) are hypotheses; the decrease conditions are not needed.
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, p. 14, Theorem 5.3, (5.4); p. 6, Assumption 2.1; p. 13, Definition 5.1 (i)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_SmallGainISS_Lyapunov_Network

open scoped NNReal

namespace SmallGainISS.Lyapunov

/-- Theorem 5.3 with (5.4) (p. 14) against Assumption 2.1 (p. 6): if every `Vᵢ` satisfies
Assumption 2.1, every `σᵢ ∈ 𝒦∞` and its inverse `τᵢ = σᵢ⁻¹` is locally Lipschitz on `(0, ∞)`
(Definition 5.1 (i)), then `V(x) = maxᵢ σᵢ⁻¹(Vᵢ(xᵢ))` satisfies Assumption 2.1 on `ℝᴺ`. -/
theorem candidate_5_4 {n : ℕ} [NeZero n] {N : Fin n → ℕ}
    (Vb : (j : Fin n) → Block N j → ℝ) (σ : ℝ≥0 → Fin n → ℝ≥0) (τ : Fin n → ℝ≥0 → ℝ≥0)
    (hV : ∀ j, IsLyapCandidate (Vb j))
    (hσ : ∀ i, IsKInf (fun r => σ r i))
    (hτ : ∀ i, IsInverse (τ i) (fun r => σ r i))
    (hτL : ∀ i, LocallyLipschitzOn (Set.Ioi (0 : ℝ≥0)) (τ i)) :
    IsLyapCandidate (netV Vb τ) := by sorry

end SmallGainISS.Lyapunov
