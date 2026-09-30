-- Prove2me | Theorems.Thm_UnderstandingML_growth_composition
-- name    : UnderstandingML.growth_composition
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:02:32.153435+00:00
-- url     : https://prove2.me/theorems/9afff8e1-90cf-48b9-bb3b-e11ee0b74206
-- title:
--   Exercise 4: the growth function of the composition class F₂ ∘ F₁ is at most τ_{F₂}(m) τ_{F₁}(m)
-- statement:
--   **Exercise 4 (Growth function of composition).** Let $F_1$ be a set of functions from $X$ to $Z$ and let $F_2$ be a set of functions from $Z$ to $Y$. Let $H = F_2 \circ F_1$ be the composition class: for every $f_1 \in F_1$ and $f_2 \in F_2$, there exists $h \in H$ such that $h(x) = f_2(f_1(x))$. Then $\tau_H(m) \le \tau_{F_2}(m)\,\tau_{F_1}(m)$. The codomains $Z, Y$ are finite.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §20.9 p. 282, Exercise 4 (used in the proof of Theorem 20.6, p. 275)

import Definitions.Def_UnderstandingML_NeuralNetworks

open MeasureTheory

namespace UnderstandingML

/-- **Exercise 4 (growth function of composition)** (p. 282). Let `F₁` be a set of functions
from `X` to `Z` and let `F₂` be a set of functions from `Z` to `Y`. Let `H = F₂ ∘ F₁` be the
composition class: for every `f₁ ∈ F₁` and `f₂ ∈ F₂`, there exists `h ∈ H` with
`h(x) = f₂(f₁(x))`. Then `τ_H(m) ≤ τ_{F₂}(m) τ_{F₁}(m)`. The codomains are finite. -/
theorem growth_composition {X Z Y : Type*} [Finite Z] [Finite Y] (F₁ : Set (X → Z))
    (F₂ : Set (Z → Y)) (m : ℕ) :
    growthY (compositionClass F₂ F₁) m ≤ growthY F₂ m * growthY F₁ m := by sorry

end UnderstandingML
