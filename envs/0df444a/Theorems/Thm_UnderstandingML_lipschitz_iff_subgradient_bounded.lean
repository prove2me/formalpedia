-- Prove2me | Theorems.Thm_UnderstandingML_lipschitz_iff_subgradient_bounded
-- name    : UnderstandingML.lipschitz_iff_subgradient_bounded
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:25:40.699528+00:00
-- url     : https://prove2.me/theorems/a8dcb214-57b6-4532-b7e1-a5e7795bef6d
-- title:
--   Lemma 14.7 (on ℝ^d): a convex f is ρ-Lipschitz iff every subgradient at every point has norm ≤ ρ
-- statement:
--   **Lemma 14.7.** Let $A$ be a convex open set and let $f : A \to \mathbb{R}$ be a convex function. Then $f$ is $\rho$-Lipschitz over $A$ iff for all $w \in A$ and $v \in \partial f(w)$ we have $\|v\| \le \rho$.
--
--   Formally: for $A = \mathbb{R}^d$ and a Lipschitz constant $\rho \ge 0$. (On $\mathbb{R}^0$, a single point, every function is $\rho$-Lipschitz for every $\rho$, while $0 \in \partial f(0)$ has norm $0$, so the equivalence needs $\rho \ge 0$.)
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §14.2.2 p. 190, Lemma 14.7 with its proof (for A = ℝ^d)

import Definitions.Def_UnderstandingML_SGD

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Lemma 14.7** (p. 190), for `A = ℝ^d`. Let `f : ℝ^d → ℝ` be a convex function. Then `f` is
`ρ`-Lipschitz iff for all `w` and `v ∈ ∂f(w)` we have `‖v‖ ≤ ρ`. The Lipschitz constant is
nonnegative: on `ℝ⁰` every function is `ρ`-Lipschitz for every `ρ`, while `0 ∈ ∂f(0)`. -/
theorem lipschitz_iff_subgradient_bounded {d : ℕ} (f : Vec d → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (∀ u v, |f u - f v| ≤ ρ * ‖u - v‖) ↔ ∀ w v, IsSubgradient f w v → ‖v‖ ≤ ρ := by sorry

end UnderstandingML
