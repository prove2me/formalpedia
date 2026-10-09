-- Prove2me | Theorems.Thm_WassTwoStage_Copositive_lemma_2
-- name    : WassTwoStage.Copositive.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:58:48.813632+00:00
-- url     : https://prove2.me/theorems/a508a771-9e92-4434-b45d-c3b63ffc7ea2
-- title:
--   Lemma 2 — completely positive decompositions yield points of Ξ and recession directions with dual-feasible companions
-- statement:
--   Fix one block $i$ of the completely positive program (14). Let $(\mu,\gamma,\Omega,\Gamma,Y)$ satisfy the $i$-th linear and quadratic constraints of (14),
--   $$\mathcal Q\mu + \boldsymbol q = \mathcal W^\top\gamma,\qquad \mathcal Q_{j:}^\top\Omega\mathcal Q_{j:} - 2\mathcal Q_{j:}^\top Y\mathcal W_{:j} + \mathcal W_{:j}^\top\Gamma\mathcal W_{:j} = \boldsymbol q_j^2\quad \forall j\in[N_2+J],$$
--   and let $(\chi_\ell,\eta_\ell,\alpha_\ell) \in \mathbb R^K_+\times\mathbb R^{M+J}_+\times\mathbb R_+$, $\ell$ in a finite index set $\mathcal L$, give the completely positive decomposition (16):
--   $$\begin{bmatrix}\Omega & Y & \mu\\ Y^\top & \Gamma & \gamma\\ \mu^\top & \gamma^\top & 1\end{bmatrix} = \sum_{\ell\in\mathcal L}\begin{bmatrix}\chi_\ell\\ \eta_\ell\\ \alpha_\ell\end{bmatrix}\begin{bmatrix}\chi_\ell\\ \eta_\ell\\ \alpha_\ell\end{bmatrix}^\top.$$
--   Let $\rho_\ell \in \mathbb R^M$ be the first $M$ entries of $\eta_\ell$. Then
--   1. for every $\ell$ with $\alpha_\ell > 0$: $\chi_\ell/\alpha_\ell \in \Xi$ and $Q(\chi_\ell/\alpha_\ell) + q = W^\top(\rho_\ell/\alpha_\ell)$;
--   2. for every $\ell$ with $\alpha_\ell = 0$: $\chi_\ell \in \mathrm{recc}(\Xi) = \{\xi\in\mathbb R^K_+ : S\xi\le 0\}$ and $Q\chi_\ell = W^\top\rho_\ell$.
--
--   The lemma turns any feasible point of (14) into discrete distributions on $\Xi$ together with feasible dual recourse solutions; it is the key step of the inequality $\mathcal Z(x) \ge \underline{\mathcal Z}(x)$ in Theorem 3.
--
--   **Formalization Note** The paper assumes the whole family $\{(\mu_i,\gamma_i,\Omega_i,\Gamma_i,Y_i)\}_{i\in[I]}$ feasible in (14); its proof uses only the $i$-th linear and quadratic constraints and the decomposition, so the statement is made for one block under those hypotheses alone, a harmless generalization. The conclusions use the original data $Q, q, W, S$ (not the extended data).
-- source:
--   Hanasusanto, Kuhn, Conic Programming Reformulations of Two-Stage Distributionally Robust Linear Programs over Wasserstein Balls, arXiv:1609.07505v3, pp. 13–14, Lemma 2; (16), p. 11; L⁺_i, L⁰_i, p. 12

import Mathlib
import Definitions.Def_WassTwoStage_Copositive_ConicPrograms

open Matrix

namespace WassTwoStage.Copositive

/-- Lemma 2, Hanasusanto–Kuhn, arXiv:1609.07505v3, pp. 13–14, for one block `i` of (14): let
`(µ, γ, Ω, Γ, Y)` satisfy the `i`-th linear and quadratic constraints of (14), and let
`(χ_ℓ, η_ℓ, α_ℓ) ∈ ℝ^K_+ × ℝ^{M+J}_+ × ℝ_+`, `ℓ ∈ L` (a finite index set), give the completely
positive decomposition (16) of the moment matrix `[[Ω, Y, µ], [Yᵀ, Γ, γ], [µᵀ, γᵀ, 1]]`. Write
`ρ_ℓ` for the first `M` entries of `η_ℓ`. Then for `α_ℓ > 0`: `χ_ℓ/α_ℓ ∈ Ξ` and
`Q(χ_ℓ/α_ℓ) + q = Wᵀ(ρ_ℓ/α_ℓ)`; and for `α_ℓ = 0`: `χ_ℓ ∈ recc(Ξ) = {ξ ∈ ℝ^K_+ : Sξ ≤ 0}` and
`Qχ_ℓ = Wᵀρ_ℓ`. -/
theorem lemma_2 {K J M N₁ N₂ I : ℕ} (d : Data K J M N₁ N₂ I) {L : Type*} [Fintype L]
    (Ω : Matrix (Fin K) (Fin K) ℝ) (Y : Matrix (Fin K) (Fin M ⊕ Fin J) ℝ) (μ : Fin K → ℝ)
    (Γ : Matrix (Fin M ⊕ Fin J) (Fin M ⊕ Fin J) ℝ) (γ : Fin M ⊕ Fin J → ℝ)
    (hlin : d.bQ *ᵥ μ + d.bq = d.bWᵀ *ᵥ γ)
    (hquad : ∀ j, d.bQ j ⬝ᵥ (Ω *ᵥ d.bQ j) - 2 * (d.bQ j ⬝ᵥ (Y *ᵥ d.bWᵀ j))
      + d.bWᵀ j ⬝ᵥ (Γ *ᵥ d.bWᵀ j) = d.bq j ^ 2)
    (χ : L → Fin K → ℝ) (η : L → Fin M ⊕ Fin J → ℝ) (α : L → ℝ)
    (hχ : ∀ l, 0 ≤ χ l) (hη : ∀ l, 0 ≤ η l) (hα : ∀ l, 0 ≤ α l)
    (hdec : cpMatrix Ω Y μ Γ γ =
      ∑ l, vecMulVec (Sum.elim (χ l) (Sum.elim (η l) (fun _ => α l)))
        (Sum.elim (χ l) (Sum.elim (η l) (fun _ => α l)))) :
    (∀ l, 0 < α l →
      WithLp.toLp 2 ((α l)⁻¹ • χ l) ∈ d.Xi ∧
      d.Q *ᵥ ((α l)⁻¹ • χ l) + d.q = d.Wᵀ *ᵥ ((α l)⁻¹ • fun m => η l (Sum.inl m))) ∧
    (∀ l, α l = 0 →
      (0 ≤ χ l ∧ d.S *ᵥ χ l ≤ 0) ∧
      d.Q *ᵥ χ l = d.Wᵀ *ᵥ fun m => η l (Sum.inl m)) := by sorry

end WassTwoStage.Copositive
