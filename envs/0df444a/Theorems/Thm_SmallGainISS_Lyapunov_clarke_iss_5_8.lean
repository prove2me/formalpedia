-- Prove2me | Theorems.Thm_SmallGainISS_Lyapunov_clarke_iss_5_8
-- name    : SmallGainISS.Lyapunov.clarke_iss_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:10:27.886981+00:00
-- url     : https://prove2.me/theorems/79735601-9fbd-4195-ae70-1d3699a9ce8a
-- title:
--   (5.8): under a strict trigger, $\langle\zeta,f_i(x,u)\rangle\le-\alpha_i(\|x_i\|)$ for all $\zeta\in\partial V_i(x_i)$
-- statement:
--   Let $V_i$ be an ISS Lyapunov function for $\Sigma_i$ (Definition 2.5) with gains $\gamma_{ij}$ ($\gamma_{ii}\equiv0$), $\gamma_{iu}$, MAF $\mu_i$ and rate $\alpha_i$, and let $f_i$ be continuous in $(x,u)$. If at $(x,u)$ the trigger of (2.7) holds strictly,
--   $$V_i(x_i)>\mu_i\big(\gamma_{i1}(V_1(x_1)),\dots,\gamma_{in}(V_n(x_n)),\gamma_{iu}(\|u\|)\big),$$
--   then for every $\zeta$ in Clarke's generalized gradient $\partial V_i(x_i)$,
--   $$\langle\zeta,f_i(x,u)\rangle\le-\alpha_i(\|x_i\|).\tag{5.8}$$
--
--   This passes from the decrease at points of differentiability (2.7) to all generalized gradients, as in the equivalence of (2.4) and (2.6) noted on p. 7; it is applied at the active indices delivered by the previous step.
--
--   **Formalization Note** Continuity of $f_i$ is the regularity behind "an equivalent formulation to (2.4) is given by (2.6)" (p. 7): (2.7) holds only at points of differentiability, and passing to limits of gradients needs it. $\partial V_i$ is the published `ClarkeGradients.Shared.generalizedGradient` on $\mathbb R^{N_i}$.
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, p. 14, proof of Theorem 5.3, (5.8); p. 7, (2.6)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_SmallGainISS_Lyapunov_Network

open scoped NNReal

namespace SmallGainISS.Lyapunov

/-- (5.8) (p. 14), the Clarke form (2.6) (p. 7) of (2.7) at a point of strict trigger: if `Vᵢ` is
an ISS Lyapunov function for `Σᵢ` with rate `αᵢ` (Definition 2.5), `fᵢ` is continuous, and
`Vᵢ(xᵢ) > μᵢ(γᵢ₁(V₁(x₁)), …, γᵢₙ(Vₙ(xₙ)), γᵢᵤ(‖u‖))` at `(x, u)`, then
`⟨ζ, fᵢ(x, u)⟩ ≤ −αᵢ(‖xᵢ‖)` for every `ζ ∈ ∂Vᵢ(xᵢ)`. -/
theorem clarke_iss_5_8 {n : ℕ} {N : Fin n → ℕ} {M : ℕ}
    (Vb : (j : Fin n) → Block N j → ℝ) (f : (i : Fin n) → State N → Input M → Block N i)
    (Γ : GainMatrix n) (γu : Fin n → ℝ≥0 → ℝ≥0) (μ : Fin n → (Fin (n + 1) → ℝ≥0) → ℝ≥0)
    (i : Fin n) (αi : ℝ≥0 → ℝ≥0)
    (hVi : IsISSLyapunovSubWith Vb f Γ γu μ i αi)
    (hΓii : Γ i i = 0)
    (hf : Continuous (fun p : State N × Input M => f i p.1 p.2))
    (x : State N) (u : Input M)
    (hstrict : μ i (issArgs Vb Γ γu i x u) < (Vb i (x i)).toNNReal) :
    ∀ ζ ∈ ClarkeGradients.Shared.generalizedGradient (Vb i) (x i),
      inner ℝ ζ (f i x u) ≤ -(αi ‖x i‖₊ : ℝ) := by sorry

end SmallGainISS.Lyapunov
