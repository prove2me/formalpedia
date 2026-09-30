-- Prove2me | Theorems.Thm_UnderstandingML_convex_smooth_bounded_learnable
-- name    : UnderstandingML.convex_smooth_bounded_learnable
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:18:34.9078+00:00
-- url     : https://prove2.me/theorems/9590ff9b-0216-4346-b44c-d469f2468973
-- title:
--   Corollary 13.11: a convex-smooth-bounded problem (β, B) with ℓ(0, z) ≤ 1 is learned by RLM with λ = ε/(3B²) once m ≥ 150βB²/ε²: E_S[L_D(A(S))] ≤ min_{w∈H} L_D(w) + ε
-- statement:
--   **Corollary 13.11.** Let $(H, Z, \ell)$ be a convex-smooth-bounded learning problem with parameters $\beta, B$. Assume in addition that $\ell(0, z) \le 1$ for all $z \in Z$. For any $\epsilon \in (0,1)$ let $m \ge \frac{150\beta B^2}{\epsilon^2}$ and set $\lambda = \epsilon/(3B^2)$. Then for every distribution $D$, $\mathbb{E}_S[L_D(A(S))] \le \min_{w \in H} L_D(w) + \epsilon$.
--
--   The book derives this from Corollary 13.10, whose stability constant $48\beta/(\lambda m)$ would need $m \ge 216\beta B^2/\epsilon^2$ in this chain. The printed $150$ is nonetheless correct, because the derivation of Corollary 13.7 is loose: with $a = \sqrt{\ell(A(S), z_i)}$, $b = \sqrt{\ell(A(S^{(i)}), z')}$ and $\lambda \ge 2\beta/m$ one has $\|A(S^{(i)}) - A(S)\| \le 2\sqrt{2\beta}(a+b)/(\lambda m)$, hence $\ell(A(S^{(i)}), z_i) - \ell(A(S), z_i) \le \frac{\beta}{\lambda m}(6a^2 + 8ab + 2b^2) \le \frac{10\beta}{\lambda m}(a^2 + b^2)$, a stability rate of $20\beta/(\lambda m)$ in place of $48\beta/(\lambda m)$. Then $\mathbb{E}[L_D(A(S))] \le \min(1, L_D(w) + \lambda\|w\|^2)(1 + 60\beta B^2/(\epsilon m)) \le L_D(w) + \epsilon/3 + 60\beta B^2/(\epsilon m)$, which is at most $L_D(w) + \epsilon$ once $m \ge 90\beta B^2/\epsilon^2$. Measurability: jointly measurable loss and measurable algorithm, with a nonnegative loss bounded at the origin so that all expectations exist (for the RLM rule the minimizer is unique, so measurability of the algorithm is automatic).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §13.4 p. 180, Corollary 13.11 (from Corollary 13.10); sample-size constant corrected from 150 to 216, see the docstring

import Definitions.Def_UnderstandingML_Convex

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Corollary 13.11** (p. 180). Let `(H, Z, ℓ)` be a convex-smooth-bounded learning problem
with parameters `β, B`, and assume `ℓ(0, z) ≤ 1` for all `z`. For `ε ∈ (0, 1)` let
`m ≥ 150 βB²/ε²` and set `λ = ε/(3B²)`. Then for every distribution `D`,
`E_S[L_D(A(S))] ≤ min_{w ∈ H} L_D(w) + ε`. Chaining Corollary 13.10 as printed (stability
constant `48β/(λm)`) would need `m ≥ 216 βB²/ε²`; the book's `150` holds because the derivation
of Corollary 13.7 gives the sharper rate `20β/(λm)` (then `m ≥ 90 βB²/ε²` suffices).
Measurability as in Corollary 13.6. -/
theorem convex_smooth_bounded_learnable {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (H : Set (Vec d)) (loss : Vec d → Z → ℝ) {β B : ℝ} (hβ : 0 < β) (hB : 0 < B)
    (hprob : ConvexSmoothBounded H loss β B) (h0 : ∀ z, loss 0 z ≤ 1) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) (m : ℕ) (hm : 150 * β * B ^ 2 / ε ^ 2 ≤ m) (A : Learner Z (Vec d))
    (hA : IsRLMLearner loss (ε / (3 * B ^ 2)) A) (hmeas : Measurable (Function.uncurry loss))
    (hAmeas : ∀ m, Measurable (A m)) (D : Measure Z) [IsProbabilityMeasure D] :
    ∀ w ∈ H, ∫ S, risk loss D (A m S) ∂(iidLaw D m) ≤ risk loss D w + ε := by sorry

end UnderstandingML
