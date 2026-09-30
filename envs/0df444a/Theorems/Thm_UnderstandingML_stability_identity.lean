-- Prove2me | Theorems.Thm_UnderstandingML_stability_identity
-- name    : UnderstandingML.stability_identity
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:15:25.332978+00:00
-- url     : https://prove2.me/theorems/662b625f-327f-424e-8d99-4a947d20bf22
-- title:
--   Theorem 13.2: E_S[L_D(A(S)) − L_S(A(S))] = E_{(S,z'),i}[ℓ(A(S⁽ⁱ⁾), zᵢ) − ℓ(A(S), zᵢ)] for any learning algorithm
-- statement:
--   **Theorem 13.2.** Let $D$ be a distribution. Let $S = (z_1, \dots, z_m)$ be an i.i.d. sequence of examples and let $z'$ be another i.i.d. example. Let $U(m)$ be the uniform distribution over $[m]$. Then, for any learning algorithm,
--   $$\mathbb{E}_{S \sim D^m}[L_D(A(S)) - L_S(A(S))] = \mathbb{E}_{(S,z') \sim D^{m+1},\, i \sim U(m)}[\ell(A(S^{(i)}), z_i) - \ell(A(S), z_i)]. \tag{13.6}$$
--
--   Formally: for $m \ge 1$, a jointly measurable loss bounded by $C$ and a measurable algorithm.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §13.2 p. 174, Theorem 13.2 with its proof

import Definitions.Def_UnderstandingML_Convex

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Theorem 13.2** (p. 174). Let `D` be a distribution, `S = (z₁, …, z_m)` an i.i.d. sequence
of examples and `z'` another i.i.d. example, and `U(m)` the uniform distribution over `[m]`.
Then for any learning algorithm,
`E_{S ∼ D^m}[L_D(A(S)) − L_S(A(S))] = E_{(S,z') ∼ D^{m+1}, i ∼ U(m)}[ℓ(A(S⁽ⁱ⁾), zᵢ) − ℓ(A(S), zᵢ)]`
(13.6). Stated for `m ≥ 1`, a jointly measurable loss bounded by `C` and a measurable
algorithm, so that all expectations exist. -/
theorem stability_identity {d : ℕ} {Z : Type*} [MeasurableSpace Z] (loss : Vec d → Z → ℝ)
    (hmeas : Measurable (Function.uncurry loss)) {C : ℝ} (hbdd : ∀ w z, |loss w z| ≤ C)
    (A : Learner Z (Vec d)) (hA : ∀ m, Measurable (A m)) (D : Measure Z)
    [IsProbabilityMeasure D] (m : ℕ) (hm : 0 < m) :
    ∫ S, (risk loss D (A m S) - empRisk loss S (A m S)) ∂(iidLaw D m) =
      (∑ i, ∫ p : (Fin m → Z) × Z,
          (loss (A m (Function.update p.1 i p.2)) (p.1 i) - loss (A m p.1) (p.1 i))
            ∂((iidLaw D m).prod D)) / m := by sorry

end UnderstandingML
