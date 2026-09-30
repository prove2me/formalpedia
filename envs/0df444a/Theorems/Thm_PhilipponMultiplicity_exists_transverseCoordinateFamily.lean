-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_transverseCoordinateFamily
-- name    : PhilipponMultiplicity.exists_transverseCoordinateFamily
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T23:31:03.214724+00:00
-- url     : https://prove2.me/theorems/bd4f5ed1-9276-42c4-a2cb-1c70ff402108
-- title:
--   Selecting transverse directions from the parameter coordinates
-- statement:
--   For analytic subgroup data with $p$ parameters and an algebraic subgroup $H$, let $c=\operatorname{codim}_A(H)$. There exist $c$ original parameter coordinate directions whose images form a basis of the parameter space modulo the inverse image of the tangent space of $H$. The empty family is allowed when $c=0$.
-- source:
--   Philippon (1986), p. 377, coordinate reindexing before the transverse multiplicity argument, https://numdam.org/articles/10.24033/bsmf.2060/.

import Definitions.Def_PhilipponMultiplicity_SectionFour
set_option autoImplicit false
open PhilipponMultiplicity

theorem PhilipponMultiplicity.exists_transverseCoordinateFamily {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}
    (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G) :
    ∃ directions : Fin (analyticCodimension A H.carrier) → Fin A.parameterDimension,
      IsTransverseCoordinateFamily A H directions := by sorry
