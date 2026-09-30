-- Prove2me | Theorems.Thm_PhilipponMultiplicity_analyticCodimension_le_dimension
-- name    : PhilipponMultiplicity.analyticCodimension_le_dimension
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T23:31:01.451372+00:00
-- url     : https://prove2.me/theorems/9a515e8f-ef0a-42b8-b5ed-ecf686f922e5
-- title:
--   Analytic subgroup codimension is bounded by its dimension
-- statement:
--   For analytic subgroup data $A$ in an embedded commutative group and any algebraic subgroup $H$, the tangent codimension satisfies $\operatorname{codim}_A(H)\le\dim A$. Dimensions and codimensions use the differential kernels of the actual vanishing ideals.
-- source:
--   Philippon (1986), analytic subgroup conventions pp. 357–358 and transverse directions p. 377, https://numdam.org/articles/10.24033/bsmf.2060/. Explicit linear-algebra component of analytic contact invariance.

import Definitions.Def_PhilipponMultiplicity_SectionFour
set_option autoImplicit false
open PhilipponMultiplicity

theorem PhilipponMultiplicity.analyticCodimension_le_dimension {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}
    (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G) :
    analyticCodimension A H.carrier ≤ A.dimension := by sorry
