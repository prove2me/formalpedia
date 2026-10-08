-- Prove2me | Theorems.Thm_SmallGainISS_Lyapunov_theorem_5_3
-- name    : SmallGainISS.Lyapunov.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:10:49.516216+00:00
-- url     : https://prove2.me/theorems/f6dd7dbe-e66b-47d3-9c29-a90c19899712
-- title:
--   Theorem 5.3 — $\max_i\sigma_i^{-1}(V_i(x_i))$ is an ISS Lyapunov function for the network
-- statement:
--   Consider the interconnected system $\Sigma:\dot x=f(x,u)$ of $n\ge1$ subsystems $\Sigma_i:\dot x_i=f_i(x,u)$, $x_i\in\mathbb R^{N_i}$, $u\in\mathbb R^M$, with each $f_i$ continuous. Assume:
--   1. each $V_i$ is an ISS Lyapunov function for $\Sigma_i$ (Definition 2.5) with gains $\gamma_{ij}\in\mathcal K_\infty\cup\{0\}$, $\gamma_{ii}\equiv0$, $\gamma_{iu}\in\mathcal K\cup\{0\}$ and MAFs $\mu_i\in\mathrm{MAF}_{n+1}$, and $\Gamma$, $\mu$ are compatible (Remark 2.6);
--   2. $\sigma$ is an Ω-path with respect to $\Gamma_\mu$ (Definition 5.1);
--   3. $\varphi\in\mathcal K_\infty$ satisfies
--   $$\overline\Gamma_\mu(\sigma(r),\varphi(r))<\sigma(r)\qquad\forall r>0,\tag{5.3}$$
--   strictly in every component, where $\overline\Gamma_\mu(s,r)_i=\mu_i(\gamma_{i1}(s_1),\dots,\gamma_{in}(s_n),\gamma_{iu}(r))$.
--
--   Then
--   $$V(x)=\max_{i=1,\dots,n}\sigma_i^{-1}(V_i(x_i))\tag{5.4}$$
--   is an ISS Lyapunov function for the overall system (Definition 2.2): it satisfies Assumption 2.1, and there is a positive definite $\alpha$ such that at every point of differentiability of $V$ and for every $u$,
--   $$V(x)\ge\varphi^{-1}(\|u\|)\ \Longrightarrow\ \nabla V(x)f(x,u)\le-\alpha(\|x\|).$$
--
--   This is the main construction of the paper: a small-gain condition, expressed through an Ω-path of the gain operator, turns ISS Lyapunov functions of the subsystems into one for the network by rescaling and maximization.
--
--   **Formalization Note** The trigger of (5.5) is corrected from the printed $V(x)\ge\max_i\varphi^{-1}(\gamma_{iu}(\|u\|))$ to $V(x)\ge\varphi^{-1}(\|u\|)$. With $\overline\Gamma_\mu$ defined by (2.9), as the paper's Corollaries 5.6–5.8 use it, the printed implication is false: for one subsystem $\dot x=-x+u/6$, $V_1=|x|$, $\gamma_{1u}(s)=s/10$, $\mu_1(a,b)=a+2b$, $\sigma=\varphi=\mathrm{id}$, (5.3) holds, but at $x=1$, $u=10$ the printed trigger holds while $\nabla V\cdot f=2/3>0$. The proof's chain closes with the corrected trigger. Continuity of each $f_i$ is the regularity behind the equivalence of (2.4) and (2.6) (p. 7) that the proof uses; it is an explicit hypothesis. The inverses $\sigma_i^{-1}$, $\varphi^{-1}$ are explicit arguments with both compositions the identity. The gain of the conclusion is $\varphi^{-1}$, which makes the conclusion of Definition 2.2 explicit.
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, pp. 13-14, Theorem 5.3, (5.3)-(5.5)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_SmallGainISS_Lyapunov_Network

open scoped NNReal

namespace SmallGainISS.Lyapunov

/-- Theorem 5.3 (pp. 13–14), with the trigger of (5.5) corrected to `V(x) ≥ φ⁻¹(‖u‖)` (the printed
trigger `maxᵢ φ⁻¹(γᵢᵤ(‖u‖))` is false under (2.9); see the mission's Formalization scope).
Each `Vᵢ` is an ISS Lyapunov function for `Σᵢ` with gains `Γ` (`γᵢᵢ ≡ 0`), `γᵢᵤ` and MAFs `μᵢ`
(Definition 2.5), compatible in the sense of Remark 2.6; `σ` is an Ω-path with respect to `Γ_μ`
with inverses `τᵢ = σᵢ⁻¹`; `φ ∈ 𝒦∞` with inverse `φ⁻¹`; (5.3) `Γ̄_μ(σ(r), φ(r)) < σ(r)` for all
`r > 0`; each `fᵢ` is continuous. Then `V(x) = maxᵢ σᵢ⁻¹(Vᵢ(xᵢ))` (5.4) is an ISS Lyapunov
function for `ẋ = f(x, u)` (Definition 2.2) with gain `φ⁻¹` and some positive definite `α`. -/
theorem theorem_5_3 {n : ℕ} [NeZero n] {N : Fin n → ℕ} {M : ℕ}
    (Vb : (j : Fin n) → Block N j → ℝ) (f : (i : Fin n) → State N → Input M → Block N i)
    (Γ : GainMatrix n) (γu : Fin n → ℝ≥0 → ℝ≥0) (μ : Fin n → (Fin (n + 1) → ℝ≥0) → ℝ≥0)
    (σ : ℝ≥0 → Fin n → ℝ≥0) (τ : Fin n → ℝ≥0 → ℝ≥0) (φ φinv : ℝ≥0 → ℝ≥0)
    (hV : ∀ i, IsISSLyapunovSub Vb f Γ γu μ i)
    (hdiag : ZeroDiagonal Γ) (hcomp : Compatible Γ μ)
    (hσ : IsOmegaPath (gainOp Γ γu μ) σ τ)
    (hφ : IsKInf φ) (hφinv : IsInverse φinv φ)
    (h53 : ∀ r : ℝ≥0, 0 < r → SLt (gainOpBar Γ γu μ (σ r) (φ r)) (σ r))
    (hf : ∀ i, Continuous (fun p : State N × Input M => f i p.1 p.2)) :
    ∃ α : ℝ≥0 → ℝ≥0, IsISSLyapunovWith (netV Vb τ) (netF f) φinv α := by sorry

end SmallGainISS.Lyapunov
