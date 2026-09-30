-- Prove2me | Theorems.Thm_UnderstandingML_sgd_learns_convex_smooth
-- name    : UnderstandingML.sgd_learns_convex_smooth
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:31:07.212249+00:00
-- url     : https://prove2.me/theorems/a81cd65d-d147-4ed4-8362-52c409b8ddba
-- title:
--   Corollary 14.14: for a convex-smooth-bounded problem (β, B) with ℓ(0,z) ≤ 1 and ε > 0, SGD with η = 1/(β(1 + 3/ε)) and T ≥ 12B²β/ε² has E[L_D(w̄)] ≤ min_{w∈H} L_D(w) + ε
-- statement:
--   **Corollary 14.14.** Consider a convex-smooth-bounded learning problem with parameters $\beta, B$. Assume in addition that $\ell(0, z) \le 1$ for all $z \in Z$. For every $\epsilon > 0$, set $\eta = \frac{1}{\beta(1 + 3/\epsilon)}$. Then running SGD with $T \ge 12B^2\beta/\epsilon^2$ yields $\mathbb{E}[L_D(\bar w)] \le \min_{w \in H} L_D(w) + \epsilon$.
--
--   Formally, as printed: every $\epsilon > 0$, with no assumption that $0 \in H$. By Theorem 14.13 with $\eta\beta = \epsilon/(\epsilon + 3)$, for every $w^\star$ one has $\mathbb{E}[L_D(\bar w)] \le (1 + \epsilon/3)(L_D(w^\star) + \|w^\star\|^2\beta(1 + 3/\epsilon)/(2T))$. Taking $w^\star = 0$ gives $\mathbb{E}[L_D(\bar w)] \le 1 + \epsilon/3$, which is at most $L_D(w) + \epsilon$ whenever $L_D(w) > 1$ or $\epsilon \ge 3/2$. Taking $w^\star = w \in H$ gives $L_D(w) + (\epsilon/3)L_D(w) + (1 + \epsilon/3)(\epsilon^2 + 3\epsilon)/24$, which is at most $L_D(w) + \epsilon$ when $L_D(w) \le 1$ and $(3 + \epsilon)^2 \le 48$, that is $\epsilon \le 3.9$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §14.5.2 p. 199, Corollary 14.14 (from Theorem 14.13)

import Definitions.Def_UnderstandingML_SGD

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Corollary 14.14** (p. 199). Consider a convex-smooth-bounded learning problem with
parameters `β, B`, and assume in addition that `ℓ(0, z) ≤ 1` for all `z`. For every `ε > 0` set
`η = 1/(β(1 + 3/ε))`. Then running SGD with `T ≥ 12B²β/ε²` yields
`E[L_D(w̄)] ≤ min_{w ∈ H} L_D(w) + ε`. From Theorem 14.13, applied with `w⋆ = w` and with
`w⋆ = 0` (which need not lie in `H`), this holds for every `ε > 0`. -/
theorem sgd_learns_convex_smooth {d : ℕ} {Z : Type*} [MeasurableSpace Z] (H : Set (Vec d))
    (loss : Vec d → Z → ℝ) {β B : ℝ} (hβ : 0 < β) (hB : 0 < B)
    (hprob : ConvexSmoothBounded H loss β B) (h0 : ∀ z, loss 0 z ≤ 1)
    (hmeas : Measurable (Function.uncurry loss))
    (hgrad : Measurable (Function.uncurry fun w z ↦ gradient (fun w ↦ loss w z) w)) {ε : ℝ}
    (hε0 : 0 < ε) (T : ℕ) (hT : 12 * B ^ 2 * β / ε ^ 2 ≤ T) (D : Measure Z)
    [IsProbabilityMeasure D] :
    ∀ w ∈ H, ∫ S, risk loss D
        (sgdAverage (1 / (β * (1 + 3 / ε))) (fun w z ↦ gradient (fun w ↦ loss w z) w) S)
        ∂(iidLaw D T) ≤ risk loss D w + ε := by sorry

end UnderstandingML
