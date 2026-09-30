-- Prove2me | Theorems.Thm_PhilipponMultiplicity_group_representative_local_rings_equiv
-- name    : PhilipponMultiplicity.group_representative_local_rings_equiv
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-29T11:12:19.825439+00:00
-- url     : https://prove2.me/theorems/bb0df0a2-71c9-4869-96db-8ad697bb158c
-- title:
--   Algebraic translations — local rings at homogeneous group representatives are isomorphic
-- statement:
--   For any two genuine homogeneous representatives r and s of points of the same embedded product G of commutative algebraic groups over an algebraically closed nontrivially normed field, the actual local coordinate rings R_mr/I(G)R_mr and R_ms/I(G)R_ms are isomorphic. This is the translation invariance step in the proof that an algebraic group is smooth. The statement includes changes of homogeneous lift. Construct the isomorphism using actual regular translation charts and invertible block scalings; no ring isomorphism, smoothness, or Cohen–Macaulay condition is included among the hypotheses.
-- source:
--   Patrice Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, Bull. Soc. Math. France 114 (1986), printed pp. 364–365 and 381–382: the ambient group is smooth, so its ideal is perfect at group points before applying Proposition 3.3. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_Operators
import Definitions.Def_PhilipponMultiplicity_Degree
set_option autoImplicit false

namespace PhilipponMultiplicity

theorem group_representative_local_rings_equiv
    (K : Type*) [NontriviallyNormedField K] [IsAlgClosed K]
    (G : EmbeddedGroupProduct K)
    (r s : GroupHomogeneousRepresentative G) :
    Nonempty (((Localization.AtPrime (representativeMaximalIdeal G r).asIdeal) ⧸
        (G.vanishingIdeal Set.univ).map (algebraMap G.CoordinateRing
          (Localization.AtPrime (representativeMaximalIdeal G r).asIdeal))) ≃+*
        ((Localization.AtPrime (representativeMaximalIdeal G s).asIdeal) ⧸
        (G.vanishingIdeal Set.univ).map (algebraMap G.CoordinateRing
          (Localization.AtPrime (representativeMaximalIdeal G s).asIdeal)))) := by sorry

end PhilipponMultiplicity
