-- Prove2me | Theorems.Thm_ProperHalfspace_corollary_20
-- name    : ProperHalfspace.corollary_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:05:40.729761+00:00
-- url     : https://prove2.me/theorems/52bf3181-e389-46d7-be9b-f65c92a543ce
-- title:
--   Corollary 20 — the loss is at most $\varepsilon/4$ with the parameters (18)
-- statement:
--   There is a universal $C_0$ such that for every $C_1\ge C_0$ and $\varepsilon\in(0,1/2)$, with the parameters $q_\varepsilon=\varepsilon/C_1$, $\rho=1-q_\varepsilon^2$, $\lambda=q_\varepsilon^6$, $\alpha=q_\varepsilon^{12}$ of (18), the following holds for every $f:\{\pm1\}^n\to[-1,1]$. Let $H\subseteq[n]$ satisfy (8), and let $E(H)\subseteq\mathbb R^{H^c}$ satisfy
--   $$v^\top M_{\mathrm{tail}}(H)v\le\lambda\qquad(v\in E(H)^\perp,\ \|v\|_2=1),$$
--   with every vector in $E(H)$ being $\eta_*$-regular, where $\eta_*=\sqrt{(1-\rho)\alpha/\lambda}$. Then every halfspace $h$ has a halfspace $g$ whose normal lies in $\mathrm{span}\{e_i:i\in H\}+E(H)$ and such that
--   $$\mathrm{corr}_f(g)\ge\mathrm{corr}_f(h)-\frac\varepsilon4.$$
--
--   Differences from the source:
--   - generalization: the target f of §4, whose type the page leaves implicit (Boolean in Theorem 1) → f : {±1}ⁿ → [−1,1]; reason: Remark 21, p.30: the structural and matrix-estimation arguments use only that f is bounded by 1; Boolean f is the special case
--   - reading: "a universal constant C₁ sufficiently large" (p.26) → ∃ C₀, ∀ C₁ ≥ C₀; reason: the stronger of the two readings; the goal's proof then picks one C₁
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), Corollary 20, pp.27–28; (18), p.26

import Mathlib
import Definitions.Def_ProperHalfspace_Halfspace
import Definitions.Def_ProperHalfspace_Regularity
import Definitions.Def_ProperHalfspace_TopEigenspace
import Definitions.Def_ProperHalfspace_HeadTail
import Definitions.Def_ProperHalfspace_Parameters

namespace ProperHalfspace

/-- Corollary 20, pp.27–28. De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344 (Nov. 1, 2026). With the parameters (18), for all sufficiently
large `C₁`: if `H` satisfies (8), `E(H) ⊆ ℝ^{Hᶜ}` has `v^⊤ M_tail(H) v ≤ λ` for every unit `v ∈ E(H)⊥`, and every vector of `E(H)` is
`η∗`-regular with `η∗ = √((1−ρ)α/λ)`, then every halfspace `h` has a halfspace `g` with normal in `span{eᵢ : i ∈ H} + E(H)` and
`corr_f(g) ≥ corr_f(h) − ε/4`.

**Formalization Note.** "A universal constant `C₁` sufficiently large" (p.26) is `∃ C₀, ∀ C₁ ≥ C₀`. -/
theorem corollary_20 : ∃ C₀ : ℝ, ∀ C₁ : ℝ, C₀ ≤ C₁ → ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
    ∀ (n : ℕ) (f : Cube n → ℝ), IsBoundedOne f →
    ∀ H : Finset (Fin n), HeadCond (rhoOf C₁ ε) (alphaOf C₁ ε) f H →
    ∀ E : Submodule ℝ (EuclideanSpace ℝ {i // i ∉ H}),
      (∀ v ∈ Eᗮ, ‖v‖ = 1 → quadForm (tailMatrix (rhoOf C₁ ε) f H) v ≤ lambdaOf C₁ ε) →
      (∀ v ∈ E, IsRegular (etaStar C₁ ε) (⇑v)) →
    ∀ (w : Fin n → ℝ) (θ : ℝ),
    ∃ (g : EuclideanSpace ℝ (Fin n)) (θ' : ℝ), g ∈ normalSpace H E ∧
      corr f (ltf w θ) - ε / 4 ≤ corr f (ltf (⇑g) θ') := by sorry

end ProperHalfspace
