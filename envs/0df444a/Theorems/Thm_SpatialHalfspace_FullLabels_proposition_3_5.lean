-- Prove2me | Theorems.Thm_SpatialHalfspace_FullLabels_proposition_3_5
-- name    : SpatialHalfspace.FullLabels.proposition_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:28:36.440199+00:00
-- url     : https://prove2.me/theorems/2baa305d-6d5c-4f6d-9186-9fe972ed7bd9
-- title:
--   Proposition 3.5 — Zero-communication improper learner
-- statement:
--   Let $D\ge 2$. For every $P^\sigma\in\mathcal M_D$, the fixed classifier $c_D=h^{(0)}\wedge h^{(1)}$, $h^{(i)}(x)=1\{\sum_e(2x_{e,i}-x_{e,1-i})>0\}$, satisfies
--
--   $$R_{\bar P^\sigma}(c_D)=2\alpha=\frac1{32}\ \le\ R^*_{\bar P^\sigma}(H_D).\tag{23}$$
--
--   In particular, the root can output $c_D$ with zero communication: on every $p$-dimensional substrate there is a legal protocol that sends no bits, so its bit-meter cost is $0$ under every input law, and whose root outputs $c_D$ on every execution.
--
--   $c_D$ depends only on $\mu_D$, not on $\sigma$; it is a conjunction of two homogeneous halfspaces, not itself a halfspace.
--
--   Differences from the source:
--
--   - reading: the root can output c_D with zero communication → for every substrate and input type there is a measurable learner, legal for every input law, with bit-meter cost 0 under every input law, whose root outputs c_D on every execution; reason: this is what outputting with zero communication means in the model of §2
--   - encoding: pairs e ∈ [q] with z_{e,0} = e_{2e−1}, z_{e,1} = e_{2e}, labels and indicators in {0,1} → e : Fin q (0-based) with basis indices 2e, 2e+1; labels and predictions in Bool, converted to 0/1 reals by bitR; reason: reindexing and identification only
-- source:
--   Yang, Spatial Communication Complexity of Agnostic Halfspace Learning, STOC 2027 submission #119 (2026), preprint, SHA-256 e5822ae144143c29214b0dab09b1a1863f55740d17b6f50ed091ddf8ffcaa692, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/119.pdf, printed p. 9, PDF p. 10, Proposition 3.5, eq. (23), PDF p. 10

import Definitions.Def_SpatialHalfspace_FullLabels_Construction

open MeasureTheory ProbabilityTheory UnderstandingML
open scoped ENNReal InnerProductSpace

namespace SpatialHalfspace.FullLabels

/-- Proposition 3.5 (Zero-communication improper learner), printed p. 9. For every
`P^σ ∈ M_D`, (23) `R_{P̄^σ}(c_D) = 2α = 1/32 ≤ R*_{P̄^σ}(H_D)`. In particular the root can output
`c_D` with zero communication: on every substrate there is a legal protocol that sends nothing,
has bit-meter cost `0` and whose root outputs `c_D`. -/
theorem proposition_3_5 (D : ℕ) (hD : 2 ≤ D) :
    (∀ σ : Term D → Bool,
      risk (mixture (PM D σ)) (cD D) = 2 * alpha ∧ 2 * alpha = 1 / 32 ∧
        2 * alpha ≤ optRisk (mixture (PM D σ))) ∧
    ∀ (p : ℕ) (S : Substrate p (Term D)) (Inp : Type) [MeasurableSpace Inp],
      ∃ Pr : Protocol S Inp (Vec D → Bool),
        (∀ ν : Measure (Term D → Inp), Pr.Legal ν ∧ Pr.BM ν = 0) ∧ Pr.IsLearner false ∧
          ∀ x R, Pr.rootOutput x R = cD D := by sorry

end SpatialHalfspace.FullLabels
