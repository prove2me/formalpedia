-- Prove2me | Theorems.Thm_UnderstandingML_gd_convex_lipschitz
-- name    : UnderstandingML.gd_convex_lipschitz
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:24:07.453522+00:00
-- url     : https://prove2.me/theorems/e570ece1-a1d3-40e9-a2cb-cb746fe0e187
-- title:
--   Corollary 14.2 (subgradient descent): for convex ρ-Lipschitz f, ‖w⋆‖ ≤ B and η = B/(ρ√T), f(w̄) − f(w⋆) ≤ Bρ/√T; T ≥ B²ρ²/ε² gives ≤ ε
-- statement:
--   **Corollary 14.2.** Let $f$ be a convex, $\rho$-Lipschitz function, and let $w^\star \in \operatorname{argmin}_{\|w\| \le B} f(w)$. If we run the GD algorithm on $f$ for $T$ steps with $\eta = \sqrt{B^2/(\rho^2 T)}$, then the output vector $\bar w$ satisfies $f(\bar w) - f(w^\star) \le B\rho/\sqrt T$. Furthermore, for every $\epsilon > 0$, to achieve $f(\bar w) - f(w^\star) \le \epsilon$ it suffices to run GD for $T \ge B^2\rho^2/\epsilon^2$ iterations. (§14.2.3: the same holds for subgradient descent.)
--
--   Formally: with directions $v_t \in \partial f(w^{(t)})$ and any $w^\star$ with $\|w^\star\| \le B$ (the proof never uses optimality of $w^\star$).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §14.1.1 p. 188, Corollary 14.2, and §14.2.3 p. 190 (subgradient descent)

import Definitions.Def_UnderstandingML_SGD

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Corollary 14.2** (p. 188), in its subgradient form (§14.2.3). Let `f` be a convex
`ρ`-Lipschitz function and let `w⋆` satisfy `‖w⋆‖ ≤ B` (the book takes a minimizer over the
ball; the bound holds for every such `w⋆`). If we run (sub)gradient descent on `f` for `T`
steps with `η = √(B²/(ρ²T))`, using at each step a subgradient `vₜ ∈ ∂f(w⁽ᵗ⁾)`, then the output
`w̄` satisfies `f(w̄) − f(w⋆) ≤ Bρ/√T`; and for every `ε > 0`, `T ≥ B²ρ²/ε²` iterations give
`f(w̄) − f(w⋆) ≤ ε`. -/
theorem gd_convex_lipschitz {d : ℕ} (f : Vec d → ℝ) (hf : ConvexOn ℝ Set.univ f) {ρ B : ℝ}
    (hρ : 0 < ρ) (hB : 0 < B) (hlip : ∀ u v, |f u - f v| ≤ ρ * ‖u - v‖) (wstar : Vec d)
    (hw : ‖wstar‖ ≤ B) (T : ℕ) (hT : 0 < T) (v : ℕ → Vec d)
    (hv : ∀ t < T, IsSubgradient f (gdIterates (B / (ρ * Real.sqrt T)) v t) (v t)) :
    f (gdAverage (B / (ρ * Real.sqrt T)) v T) - f wstar ≤ B * ρ / Real.sqrt T ∧
    ∀ ε : ℝ, 0 < ε → B ^ 2 * ρ ^ 2 / ε ^ 2 ≤ T →
      f (gdAverage (B / (ρ * Real.sqrt T)) v T) - f wstar ≤ ε := by sorry

end UnderstandingML
