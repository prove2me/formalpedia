-- Prove2me | Theorems.Thm_ProperHalfspace_theorem_18
-- name    : ProperHalfspace.theorem_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:05:26.801817+00:00
-- url     : https://prove2.me/theorems/808d441c-d4c5-4936-bd24-f095e2f1c8ee
-- title:
--   Theorem 18 — a common subspace for competitors of every halfspace
-- statement:
--   Fix $\rho\in(0,1)$ and $f:\{\pm1\}^n\to[-1,1]$. Let $\alpha\in(0,1)$ and $\lambda,\eta_E>0$, let $H$ satisfy (8), and let $E\subseteq\mathbb R^{H^c}$ satisfy
--   $$v^\top M_{\mathrm{tail}}(H)v\le\lambda\qquad(v\in E^\perp,\ \|v\|_2=1),$$
--   with every vector in $E$ being $\eta_E$-regular. For every $\tau,\nu\in(0,1/2)$ and every halfspace $h$ there is a halfspace $g$ whose normal belongs to $\mathrm{span}\{e_i:i\in H\}+E$ and such that
--   $$\mathrm{corr}_f(g)\ge\mathrm{corr}_f(h)-\Delta_{\mathrm{str}}(\rho,\alpha,\tau,\nu,\lambda,\eta_E),$$
--   with the constant $C_0$ of $\Delta_{\mathrm{str}}$ universal. Here $E$ is identified with its embedding in $\mathbb R^n$ supported on $H^c$, and $E^\perp$ is taken inside $\mathbb R^{H^c}$.
--
--   The subspace depends only on $f$, not on $h$, and this reduces the search to a low-dimensional one.
--
--   Differences from the source:
--   - generalization: the target f of §4, whose type the page leaves implicit (Boolean in Theorem 1) → f : {±1}ⁿ → [−1,1]; reason: Remark 21, p.30: the structural and matrix-estimation arguments use only that f is bounded by 1; Boolean f is the special case
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), Theorem 18, p.23; (11), p.23; standing ρ ∈ (0,1) of §4.1, p.21

import Mathlib
import Definitions.Def_ProperHalfspace_Halfspace
import Definitions.Def_ProperHalfspace_Regularity
import Definitions.Def_ProperHalfspace_TopEigenspace
import Definitions.Def_ProperHalfspace_HeadTail
import Definitions.Def_ProperHalfspace_Parameters

namespace ProperHalfspace

/-- Theorem 18, p.23. De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344 (Nov. 1, 2026). With `C₀` of (11) universal, for `ρ, α ∈ (0, 1)`,
`λ, η_E > 0`, `H` satisfying (8), and `E ⊆ ℝ^{Hᶜ}` with `v^⊤ M_tail(H) v ≤ λ` for every unit `v ∈ E⊥` and every vector of `E` being
`η_E`-regular: for `τ, ν ∈ (0, 1/2)` and every halfspace `h` there is a halfspace `g` with normal in `span{eᵢ : i ∈ H} + E` and
`corr_f(g) ≥ corr_f(h) − Δ_str(ρ, α, τ, ν, λ, η_E)`.

**Formalization Note.** `ρ ∈ (0, 1)` is the standing assumption of §4.1, p.21. `E⊥` is taken inside `ℝ^{Hᶜ}`. -/
theorem theorem_18 : ∃ C₀ : ℝ, ∀ (n : ℕ) (f : Cube n → ℝ), IsBoundedOne f →
    ∀ ρ α lamE ηE : ℝ, 0 < ρ → ρ < 1 → 0 < α → α < 1 → 0 < lamE → 0 < ηE →
    ∀ H : Finset (Fin n), HeadCond ρ α f H →
    ∀ E : Submodule ℝ (EuclideanSpace ℝ {i // i ∉ H}),
      (∀ v ∈ Eᗮ, ‖v‖ = 1 → quadForm (tailMatrix ρ f H) v ≤ lamE) →
      (∀ v ∈ E, IsRegular ηE (⇑v)) →
    ∀ τ ν : ℝ, 0 < τ → τ < 1 / 2 → 0 < ν → ν < 1 / 2 →
    ∀ (w : Fin n → ℝ) (θ : ℝ),
    ∃ (g : EuclideanSpace ℝ (Fin n)) (θ' : ℝ), g ∈ normalSpace H E ∧
      corr f (ltf w θ) - deltaStr C₀ ρ α τ ν lamE ηE ≤ corr f (ltf (⇑g) θ') := by sorry

end ProperHalfspace
