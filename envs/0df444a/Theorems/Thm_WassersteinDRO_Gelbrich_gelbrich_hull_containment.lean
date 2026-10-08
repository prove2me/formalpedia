-- Prove2me | Theorems.Thm_WassersteinDRO_Gelbrich_gelbrich_hull_containment
-- name    : WassersteinDRO.Gelbrich.gelbrich_hull_containment
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-21T02:28:55.331433+00:00
-- url     : https://prove2.me/theorems/d5fc0224-5cf3-46a9-97c7-165e027e6032
-- title:
--   Theorem 13 — Gelbrich hull
-- statement:
--   If the nominal distribution $\hat P_N$ has mean vector $\hat\mu \in \mathbb{R}^m$ and
--   covariance matrix $\hat\Sigma \in S^m_+$, then $B_{\varepsilon,p}(\hat P_N) \subseteq
--   G_\varepsilon(\hat\mu,\hat\Sigma)$ for every $p \ge 2$: the Gelbrich hull is an outer
--   approximation of every type-$p$ Wasserstein ball with $p \ge 2$, using only first- and
--   second-order moment information about the nominal distribution.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, Theorem 13, p. 18

import Mathlib
import Definitions.Def_WassersteinDRO_Gelbrich_ambiguitySet
import Definitions.Def_WassersteinDRO_Gelbrich_gelbrichHull

open MeasureTheory

namespace WassersteinDRO.Gelbrich

/-- Theorem 13 (Gelbrich hull), Kuhn et al. 2019, p. 18 — the goal theorem: if the nominal
distribution `P̂N` has mean vector `μ̂` and covariance matrix `Ŝ`, then the Wasserstein
ambiguity set is contained in the Gelbrich hull, `B_{ε,p}(P̂N) ⊆ G_ε(μ̂,Ŝ)`, for every `p ≥ 2`.
This is the outer approximation that Corollary 1 turns into a tractable upper bound on the
worst-case risk, and that Theorem 16 (not formalized in this chunk — see `STATUS.md`) sharpens
to an equality for quadratic losses and elliptical nominal distributions. -/
theorem gelbrich_hull_containment {m : ℕ} (ε p : ℝ) (hp : 2 ≤ p)
    (Ξ : Set (EuclideanSpace ℝ (Fin m))) (PN : Measure (EuclideanSpace ℝ (Fin m)))
    (μhat : EuclideanSpace ℝ (Fin m)) (SigmaHat : Matrix (Fin m) (Fin m) ℝ)
    (hμ : meanVector PN = μhat) (hS : covarianceMatrix PN = SigmaHat) :
    ambiguitySet ε p Ξ PN ⊆ gelbrichHull ε Ξ μhat SigmaHat := by sorry

end WassersteinDRO.Gelbrich
