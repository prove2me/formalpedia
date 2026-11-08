-- Prove2me | Theorems.Thm_ProperHalfspace_lemma_17
-- name    : ProperHalfspace.lemma_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:05:37.628811+00:00
-- url     : https://prove2.me/theorems/26a967a4-e56e-4d54-a0e3-6570a9d56a4e
-- title:
--   Lemma 17 — regularizing the tail
-- statement:
--   Fix $\rho\in(0,1)$ and $f:\{\pm1\}^n\to[-1,1]$. Let $\alpha\in(0,1)$, let $H$ satisfy $\mathrm{Inf}_i[f^{\mathrm{sm}}]\le\rho\alpha$ for all $i\in H^c$, and let $h(x)=\operatorname{sign}(w_H\cdot x_H+w_{H^c}\cdot x_{H^c}-\theta)$. For every $\tau,\nu\in(0,1/2)$ there is a halfspace
--   $$h^*(x)=\operatorname{sign}(w_H\cdot x_H+u\cdot x_{H^c}-\theta^*)$$
--   with the same head coefficients, whose tail normal $u$ is zero or $\tau$-regular, and such that
--   $$\mathrm{corr}_{f^{\mathrm{sm}}}(h^*)\ge\mathrm{corr}_{f^{\mathrm{sm}}}(h)-C\Bigl(\nu+\frac{\sqrt{\alpha\log(1/\nu)\Lambda_\nu}}\tau\Bigr),$$
--   where $C$ is universal.
--
--   Differences from the source:
--   - generalization: the target f of §4, whose type the page leaves implicit (Boolean in Theorem 1) → f : {±1}ⁿ → [−1,1]; reason: Remark 21, p.30: the structural and matrix-estimation arguments use only that f is bounded by 1; Boolean f is the special case
--   - encoding: "C" in the display → one C chosen before all the data; reason: the page's constants are universal (p.10)
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), Lemma 17, p.22; standing ρ ∈ (0,1) of §4.1, p.21

import Mathlib
import Definitions.Def_ProperHalfspace_Halfspace
import Definitions.Def_ProperHalfspace_Regularity
import Definitions.Def_ProperHalfspace_HeadTail

namespace ProperHalfspace

/-- Lemma 17, p.22 (regularizing the tail). De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344 (Nov. 1, 2026). With `C` universal, for
`ρ, α ∈ (0, 1)`, `H` satisfying (8), and `τ, ν ∈ (0, 1/2)`: every `h = sign(w_H · x_H + w_{Hᶜ} · x_{Hᶜ} − θ)` has a halfspace
`h∗ = sign(w_H · x_H + u · x_{Hᶜ} − θ∗)` with the same `w_H`, whose tail normal `u` is zero or `τ`-regular, and
`corr_{f^sm}(h∗) ≥ corr_{f^sm}(h) − C (ν + √(α log(1/ν) Λ_ν)/τ)`.

**Formalization Note.** `ρ ∈ (0, 1)` is the standing assumption of §4.1, p.21. -/
theorem lemma_17 : ∃ C : ℝ, ∀ (n : ℕ) (f : Cube n → ℝ), IsBoundedOne f →
    ∀ ρ α : ℝ, 0 < ρ → ρ < 1 → 0 < α → α < 1 → ∀ H : Finset (Fin n), HeadCond ρ α f H →
    ∀ (w : Fin n → ℝ) (θ τ ν : ℝ), 0 < τ → τ < 1 / 2 → 0 < ν → ν < 1 / 2 →
    ∃ (u : {i // i ∉ H} → ℝ) (θ' : ℝ), IsRegular τ u ∧
      corr (smooth ρ f) (ltf w θ) - C * (ν + Real.sqrt (α * Real.log (1 / ν) * lam ν) / τ) ≤
        corr (smooth ρ f) (ltf (glue H w u) θ') := by sorry

end ProperHalfspace
