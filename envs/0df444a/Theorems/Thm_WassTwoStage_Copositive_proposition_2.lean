-- Prove2me | Theorems.Thm_WassTwoStage_Copositive_proposition_2
-- name    : WassTwoStage.Copositive.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:58:37.320239+00:00
-- url     : https://prove2.me/theorems/cc122041-331e-4b21-8d08-a64844612981
-- title:
--   Proposition 2 — $\overline{\mathcal Z}_\delta(x) = \underline{\mathcal Z}_\delta(x)$ is finite for $\delta > 0$ and tends to $\mathcal Z(x)$ as $\delta \downarrow 0$
-- statement:
--   Assume the setting of §3 ($\Xi \ne \emptyset$, sufficiently expensive recourse, $I\ge1$, $\hat\xi_i\in\Xi$, $\epsilon\ge0$). Fix a first-stage decision $x$. Then:
--   1. for every $\delta > 0$, the copositive program (24) and the completely positive program (25) have the same optimal value, and it is finite:
--   $$\overline{\mathcal Z}_\delta(x) = \underline{\mathcal Z}_\delta(x) \in \mathbb R;$$
--   2. as $\delta$ decreases to $0$,
--   $$\lim_{\delta\downarrow0}\overline{\mathcal Z}_\delta(x) = \mathcal Z(x).$$
--
--   Here (24) is the copositive program (10) with $\delta\mathbb I$ added to the middle diagonal block, and (25) is the completely positive program (14) with $-\delta\,\mathrm{tr}(\Gamma_i)$ added to the $i$-th summand of the objective. Without complete recourse, the perturbation $\delta > 0$ thus restores strong duality, at the price of an approximation that becomes exact in the limit.
--
--   **Formalization Note** "Finite" means different from $+\infty$ and $-\infty$ in `EReal`. The limit is one-sided, $\delta \to 0^+$, and is taken in the order topology of $[-\infty,+\infty]$, so it is meaningful also when $\mathcal Z(x) = +\infty$. "For any fixed $x\in\mathcal X$" is stated for every $x \in \mathbb R^{N_1}$.
-- source:
--   Hanasusanto, Kuhn, Conic Programming Reformulations of Two-Stage Distributionally Robust Linear Programs over Wasserstein Balls, arXiv:1609.07505v3, p. 17, Proposition 2, (24), (25); proof pp. 17–18

import Mathlib
import Definitions.Def_WassTwoStage_Copositive_ConicPrograms

open Filter Topology

namespace WassTwoStage.Copositive

/-- Proposition 2, Hanasusanto–Kuhn, arXiv:1609.07505v3, p. 17 (proof pp. 17–18): under the
standing assumptions of §3, for every first-stage decision `x` and every `δ > 0` the copositive
program (24) and the completely positive program (25) have the same, finite, optimal value
`𝒵̄_δ(x) = 𝒵̲_δ(x)`, and `𝒵̄_δ(x) → 𝒵(x)` as `δ ↓ 0`. -/
theorem proposition_2 {K J M N₁ N₂ I : ℕ} (d : Data K J M N₁ N₂ I) (hI : 0 < I)
    (hXi : d.Xi.Nonempty) (hSER : d.SufficientlyExpensiveRecourse)
    (hξ : ∀ i, d.ξhat i ∈ d.Xi) (hε : 0 ≤ d.ε) (x : Fin N₁ → ℝ) :
    (∀ δ : ℝ, 0 < δ →
      d.upperValue δ x = d.lowerValue δ x ∧ d.upperValue δ x ≠ ⊤ ∧ d.upperValue δ x ≠ ⊥) ∧
    Tendsto (fun δ => d.upperValue δ x) (𝓝[>] 0) (𝓝 (d.worstCase x)) := by sorry

end WassTwoStage.Copositive
