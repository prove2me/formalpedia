-- Prove2me | Theorems.Thm_SparseIncidenceHom_WidthComparison_fhw_bounds_of_adaptive_width
-- name    : SparseIncidenceHom.WidthComparison.fhw_bounds_of_adaptive_width
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:56.173367+00:00
-- url     : https://prove2.me/theorems/91369d79-c9b5-4353-816c-3d26b8a9cb8c
-- title:
--   Theorem 1.1 — fractional hypertree width bounds from adaptive width
-- statement:
--   There exists a universal constant $C>0$ such that every finite nonempty connected covered hypergraph $H$ satisfies the following bounds. Write $a=\operatorname{adw}(H)$, let $\mu(H)$ be its incidence degeneracy, and let $\alpha(H)$ be the independence number of its primal graph. If $a\ge2$, then both
--   $$\operatorname{fhw}(H)\le C\mu(H)a\log_2 a,\qquad
--   \operatorname{fhw}(H)\le C\max\{1,\log_2\alpha(H)\}a\log_2 a.$$
--   If $a<2$, then both
--   $$\operatorname{fhw}(H)\le C\mu(H),\qquad
--   \operatorname{fhw}(H)\le C\max\{1,\log_2\alpha(H)\}.$$
--   The same constant works across all hypergraphs, both structural factors, and both width regimes. The two widths are independently optimized from their source definitions. There is no complexity assumption or bound on rank, degree, size, independence, or degeneracy. This is the full unconditional structural width comparison used in the submission's homomorphism consequences.
--
--   Differences from the source:
--   - encoding: finite hypergraphs with the standing coverage and nonempty-edge conventions → Mathlib hypergraphs on an arbitrary finite carrier, with the full carrier as vertex set and explicit coverage and nonempty-edge fields; reason: every source hypergraph is represented by choosing its vertex set as carrier, including empty and disconnected induced hypergraphs
--   - encoding: minimum over tree decompositions and fractional covers → real infima of their attained cost sets; finite bag maxima and bounded modular suprema; reason: finite covered hypergraphs have feasible covers and decompositions, all relevant costs are bounded, and the minima are attained
-- source:
--   Matthias Lanzinger, STOC 2027 submission #662 (October 2026), p. 4, Theorem 1.1; restated p. 13 and proved p. 14

import Mathlib
import Definitions.Def_SparseIncidenceHom_WidthComparison_Separators

namespace SparseIncidenceHom.WidthComparison

theorem fhw_bounds_of_adaptive_width :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] (H : FiniteHypergraph V),
      InputHypergraph H →
      (2 ≤ adaptiveWidth H →
        fractionalHypertreeWidth H ≤ C * (incidenceDegeneracy H : ℝ) * adaptiveWidth H *
          logTwo (adaptiveWidth H) ∧
        fractionalHypertreeWidth H ≤ C * max 1 (logTwo (independenceNumber H : ℝ)) *
          adaptiveWidth H * logTwo (adaptiveWidth H)) ∧
      (adaptiveWidth H < 2 →
        fractionalHypertreeWidth H ≤ C * (incidenceDegeneracy H : ℝ) ∧
        fractionalHypertreeWidth H ≤ C * max 1 (logTwo (independenceNumber H : ℝ))) := by sorry

end SparseIncidenceHom.WidthComparison
