-- Prove2me | Theorems.Thm_SmallGainISS_Lyapunov_chain_rule
-- name    : SmallGainISS.Lyapunov.chain_rule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:10:28.394975+00:00
-- url     : https://prove2.me/theorems/766d46ae-086a-4ac2-83be-3c1d38f0f574
-- title:
--   Proof of Theorem 5.3, p. 14: $\partial(\sigma_i^{-1}\circ V_i)(x_i)\subset\{c\zeta\}$, $c$ bounded away from zero
-- statement:
--   Let $\sigma$ be an Ω-path (Definition 5.1) with inverses $\sigma_i^{-1}$, let $V_i$ satisfy Assumption 2.1, and let $x_i\ne0$. Then
--   1. $\partial(\sigma_i^{-1}\circ V_i)(x_i)\subset\{c\zeta : c\in\partial\sigma_i^{-1}(y),\ y=V_i(x_i),\ \zeta\in\partial V_i(x_i)\}$;
--   2. the number $c$ is bounded away from zero: for every compact $K\subset(0,\infty)$ there is $c_0>0$ with $c\ge c_0$ for every $y\in K$ and every $c\in\partial\sigma_i^{-1}(y)$.
--
--   $$\partial(\sigma_i^{-1}\circ V_i)(x_i)\subset\{c\zeta : c\in\partial\sigma_i^{-1}(V_i(x_i)),\ \zeta\in\partial V_i(x_i)\}.$$
--
--   This is the chain rule for Lipschitz functions as used on p. 14; the lower bound on $c$, from (5.1), is what turns the decrease rate $\alpha_i$ of $V_i$ into a decrease rate of $\sigma_i^{-1}\circ V_i$.
--
--   **Formalization Note** $\partial V_i$ and $\partial(\sigma_i^{-1}\circ V_i)$ on $\mathbb R^{N_i}$ use the published `ClarkeGradients.Shared.generalizedGradient`; $\partial\sigma_i^{-1}$ on $\mathbb R$ uses `clarkeGrad` applied to $r\mapsto\sigma_i^{-1}(\max(r,0))$. The inclusion is stated without a convex hull, as on the page; it is the case here because every $c$ is positive.
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, p. 14, proof of Theorem 5.3 (chain rule after (5.8)); (5.1) p. 13

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_SmallGainISS_Lyapunov_Network

open scoped NNReal

namespace SmallGainISS.Lyapunov

/-- The chain rule step of the proof of Theorem 5.3 (p. 14), for an Ω-path `σ` with inverses
`τᵢ = σᵢ⁻¹` (Definition 5.1) and `Vᵢ` satisfying Assumption 2.1, at `xᵢ ≠ 0`:
(a) `∂(σᵢ⁻¹ ∘ Vᵢ)(xᵢ) ⊂ {cζ : c ∈ ∂σᵢ⁻¹(y), y = Vᵢ(xᵢ), ζ ∈ ∂Vᵢ(xᵢ)}`;
(b) "the number `c` is bounded away from zero because of (5.1)": for every compact
`K ⊂ (0, ∞)` there is `c₀ > 0` with `c₀ ≤ c` for all `y ∈ K` and `c ∈ ∂σᵢ⁻¹(y)`. -/
theorem chain_rule {n : ℕ} {N : Fin n → ℕ}
    (Vb : (j : Fin n) → Block N j → ℝ) (T : (Fin n → ℝ≥0) → (Fin n → ℝ≥0))
    (σ : ℝ≥0 → Fin n → ℝ≥0) (τ : Fin n → ℝ≥0 → ℝ≥0)
    (hσ : IsOmegaPath T σ τ) (i : Fin n) (hVi : IsLyapCandidate (Vb i))
    (xi : Block N i) (hxi : xi ≠ 0) :
    ClarkeGradients.Shared.generalizedGradient (fun z => liftR (τ i) (Vb i z)) xi ⊆
        {v | ∃ c ∈ clarkeGrad (liftR (τ i)) (Vb i xi),
          ∃ ζ ∈ ClarkeGradients.Shared.generalizedGradient (Vb i) xi, v = c • ζ} ∧
      ∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioi 0 →
        ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ y ∈ K, ∀ c ∈ clarkeGrad (liftR (τ i)) y, c₀ ≤ c := by sorry

end SmallGainISS.Lyapunov
