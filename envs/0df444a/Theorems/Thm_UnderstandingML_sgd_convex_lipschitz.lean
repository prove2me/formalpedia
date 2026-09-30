-- Prove2me | Theorems.Thm_UnderstandingML_sgd_convex_lipschitz
-- name    : UnderstandingML.sgd_convex_lipschitz
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:26:24.991402+00:00
-- url     : https://prove2.me/theorems/a5cb60f0-5852-4711-97b9-fc5f5a6e63f8
-- title:
--   Theorem 14.8 (SGD): for convex f, an oracle with E_z g(w,z) ∈ ∂f(w) and ‖g‖ ≤ ρ, ‖w⋆‖ ≤ B and η = B/(ρ√T): E[f(w̄)] − f(w⋆) ≤ Bρ/√T; T ≥ B²ρ²/ε² gives ≤ ε
-- statement:
--   **Theorem 14.8.** Let $B, \rho > 0$. Let $f$ be a convex function and let $w^\star \in \operatorname{argmin}_{\|w\| \le B} f(w)$. Assume that SGD is run for $T$ iterations with $\eta = \sqrt{B^2/(\rho^2 T)}$. Assume also that for all $t$, $\|v_t\| \le \rho$ with probability $1$. Then $\mathbb{E}[f(\bar w)] - f(w^\star) \le B\rho/\sqrt T$. Therefore, for any $\epsilon > 0$, to achieve $\mathbb{E}[f(\bar w)] - f(w^\star) \le \epsilon$ it suffices to run SGD for $T \ge B^2\rho^2/\epsilon^2$ iterations.
--
--   Formally: the random directions are $v_t = g(w^{(t)}, z_t)$ for i.i.d. $z_t \sim D$ and a measurable oracle $g$ with $\mathbb{E}_z g(w, z) \in \partial f(w)$ for every $w$ (the book's $\mathbb{E}[v_t \mid w^{(t)}] \in \partial f(w^{(t)})$) and $\|g(w,z)\| \le \rho$; the bound holds for every $w^\star$ with $\|w^\star\| \le B$; the expectation is over $D^T$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §14.3.1 pp. 192-193, Theorem 14.8 with its proof

import Definitions.Def_UnderstandingML_SGD

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Theorem 14.8** (p. 192). Let `B, ρ > 0`. Let `f` be a convex function and let `w⋆` satisfy
`‖w⋆‖ ≤ B` (the book takes a minimizer over the ball; the bound holds for every such `w⋆`).
Assume that SGD is run for `T` iterations with `η = √(B²/(ρ²T))`, with directions
`vₜ = g(w⁽ᵗ⁾, zₜ)` for i.i.d. `zₜ ∼ D` and an oracle `g` whose expectation `E_z g(w, z)` is a
subgradient of `f` at `w`, and that `‖vₜ‖ ≤ ρ`. Then `E[f(w̄)] − f(w⋆) ≤ Bρ/√T`; and for any
`ε > 0`, `T ≥ B²ρ²/ε²` iterations give `E[f(w̄)] − f(w⋆) ≤ ε`. -/
theorem sgd_convex_lipschitz {d : ℕ} {Z : Type*} [MeasurableSpace Z] (f : Vec d → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (D : Measure Z) [IsProbabilityMeasure D]
    (g : Vec d → Z → Vec d) (hg : Measurable (Function.uncurry g))
    (horacle : IsSubgradientOracle f D g) {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B)
    (hbound : ∀ w z, ‖g w z‖ ≤ ρ) (wstar : Vec d) (hw : ‖wstar‖ ≤ B) (T : ℕ) (hT : 0 < T) :
    (∫ S, f (sgdAverage (B / (ρ * Real.sqrt T)) g S) ∂(iidLaw D T)) - f wstar ≤
        B * ρ / Real.sqrt T ∧
    ∀ ε : ℝ, 0 < ε → B ^ 2 * ρ ^ 2 / ε ^ 2 ≤ T →
      (∫ S, f (sgdAverage (B / (ρ * Real.sqrt T)) g S) ∂(iidLaw D T)) - f wstar ≤ ε := by sorry

end UnderstandingML
