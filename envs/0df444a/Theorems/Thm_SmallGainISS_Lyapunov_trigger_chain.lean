-- Prove2me | Theorems.Thm_SmallGainISS_Lyapunov_trigger_chain
-- name    : SmallGainISS.Lyapunov.trigger_chain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:10:35.355886+00:00
-- url     : https://prove2.me/theorems/ce8a628e-4f60-428f-8cee-65cb75ad8a29
-- title:
--   Proof of Theorem 5.3, p. 14: at an active index the trigger of (2.7) holds strictly
-- statement:
--   Let the gains satisfy $\gamma_{ij}\in\mathcal K_\infty\cup\{0\}$, $\gamma_{iu}\in\mathcal K\cup\{0\}$, $\mu_i\in\mathrm{MAF}_{n+1}$, let $V_1,\dots,V_n$ satisfy Assumption 2.1, let $\sigma_i\in\mathcal K_\infty$ with inverses $\sigma_i^{-1}$, and let $\varphi\in\mathcal K_\infty$ with inverse $\varphi^{-1}$ satisfy
--   $$\overline\Gamma_\mu(\sigma(r),\varphi(r))<\sigma(r)\quad\text{for all } r>0,\tag{5.3}$$
--   strictly in every component. Let $V(x)=\max_j\sigma_j^{-1}(V_j(x_j))$, let $x\ne0$, let $i$ be active at $x$ ($V(x)=\sigma_i^{-1}(V_i(x_i))$), and let $u$ satisfy $V(x)\ge\varphi^{-1}(\|u\|)$. Then
--   $$V_i(x_i)>\mu_i\big(\gamma_{i1}(V_1(x_1)),\dots,\gamma_{in}(V_n(x_n)),\gamma_{iu}(\|u\|)\big).$$
--
--   This is the chain of inequalities on p. 14 of the proof of Theorem 5.3, for a general active index instead of "without loss of generality $i=1$": it shows that the ISS condition (2.7) of subsystem $i$ is triggered.
--
--   **Formalization Note** The trigger is $V(x)\ge\varphi^{-1}(\|u\|)$, not the printed $V(x)\ge\max_i\varphi^{-1}(\gamma_{iu}(\|u\|))$. With $\overline\Gamma_\mu$ as defined in (2.9), the last slot of (5.3) is $\gamma_{iu}(\varphi(r))$; the second line of the printed chain writes $\varphi(r)$ instead. With the printed trigger and (5.3) read through (2.9) the claim is false (one subsystem, $\gamma_{1u}(s)=s/10$, $\mu_1(a,b)=a+2b$, $\varphi=\sigma=\mathrm{id}$, $V_1=|x|$, $u=10$, $x=1$), so the trigger is corrected to the one under which the paper's chain closes ($\|u\|\le\varphi(r)\Rightarrow\gamma_{iu}(\|u\|)\le\gamma_{iu}(\varphi(r))$).
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, p. 14, proof of Theorem 5.3 (chain of inequalities after (5.7)); (5.3) p. 13; (2.9) p. 8

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_SmallGainISS_Lyapunov_Network

open scoped NNReal

namespace SmallGainISS.Lyapunov

/-- The chain of inequalities in the proof of Theorem 5.3 (p. 14), for a general active index:
let `x ≠ 0`, `i ∈ I` (5.6), `r := V(x)`, and assume (5.3) `Γ̄_μ(σ(r), φ(r)) < σ(r)` for all
`r > 0` (strict in every component) and the trigger `V(x) ≥ φ⁻¹(‖u‖)` (the corrected trigger of
(5.5), see the mission's Formalization scope). Then the trigger of (2.7) holds strictly at
`(x, u)`: `Vᵢ(xᵢ) > μᵢ(γᵢ₁(V₁(x₁)), …, γᵢₙ(Vₙ(xₙ)), γᵢᵤ(‖u‖))`. -/
theorem trigger_chain {n : ℕ} [NeZero n] {N : Fin n → ℕ} {M : ℕ}
    (Vb : (j : Fin n) → Block N j → ℝ) (Γ : GainMatrix n) (γu : Fin n → ℝ≥0 → ℝ≥0)
    (μ : Fin n → (Fin (n + 1) → ℝ≥0) → ℝ≥0) (σ : ℝ≥0 → Fin n → ℝ≥0)
    (τ : Fin n → ℝ≥0 → ℝ≥0) (φ φinv : ℝ≥0 → ℝ≥0)
    (hV : ∀ j, IsLyapCandidate (Vb j))
    (hμ : ∀ i, IsMAF (μ i))
    (hΓ : ∀ i j, IsKInfOrZero (Γ i j)) (hγu : ∀ i, IsKOrZero (γu i))
    (hσ : ∀ i, IsKInf (fun r => σ r i))
    (hτ : ∀ i, IsInverse (τ i) (fun r => σ r i))
    (hφ : IsKInf φ) (hφinv : IsInverse φinv φ)
    (h53 : ∀ r : ℝ≥0, 0 < r → SLt (gainOpBar Γ γu μ (σ r) (φ r)) (σ r))
    (x : State N) (u : Input M) (i : Fin n) (hx : x ≠ 0) (hi : i ∈ activeSet Vb τ x)
    (htrig : (φinv ‖u‖₊ : ℝ) ≤ netV Vb τ x) :
    μ i (issArgs Vb Γ γu i x u) < (Vb i (x i)).toNNReal := by sorry

end SmallGainISS.Lyapunov
