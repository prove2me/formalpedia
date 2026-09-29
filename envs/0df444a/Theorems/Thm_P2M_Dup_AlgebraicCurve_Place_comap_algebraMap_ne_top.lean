-- Prove2me | Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_comap_algebraMap_ne_top
-- name    : P2M.Dup.AlgebraicCurve.Place.comap_algebraMap_ne_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/c19d159f-de48-5b2c-9cc0-afc391524002
-- title:
--   Restriction of a place along an integral extension is proper
-- statement:
--   Let $K$, $F$ and $F'$ be fields, with $F'$ an algebra over $K$ and an algebra over $F$ (no compatibility between these two structures is assumed). Let $w$ be a place of $F'$ over $K$ in the sense of the project, i.e. a valuation subring $\mathcal{O}_w \subseteq F'$ together with the data that the image of $K$ under the structure map $K \to F'$ is contained in $\mathcal{O}_w$, that $\mathcal{O}_w \neq F'$, and that $\mathcal{O}_w$ is a principal ideal ring. Assume further that $F'$ is integral over $F$, that is, every element of $F'$ is integral over $F$ via the structure map $F \to F'$. The assertion is that the preimage of $\mathcal{O}_w$ under the structure map $F \to F'$, regarded as a valuation subring of $F$, is not the top valuation subring $F$ itself; equivalently, some element of $F$ has image in $F'$ outside $\mathcal{O}_w$. Among the clauses constituting $w$, the proof uses only the properness clause $\mathcal{O}_w \neq F'$.
--
--   This is the standard fact that a nontrivial place of $F'$ restricts to a nontrivial place of a subfield over which $F'$ is integral, so that the valuation of $w$ does not become trivial on $F$. It is used in the construction of places of the function field of a modular curve obtained by restricting places of a larger field, in [`ModularCurve.exists_place_qExpFunctionFieldC_galoisField_toValuationSubring_eq_comap_and_deg_eq_one`](thm.html#ModularCurve.exists_place_qExpFunctionFieldC_galoisField_toValuationSubring_eq_comap_and_deg_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_comap_algebraMap_ne_top.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem P2M.Dup.AlgebraicCurve.Place.comap_algebraMap_ne_top {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F'] [Algebra F F'] (w : Place K F') [Algebra.IsIntegral F F'] :
    w.toValuationSubring.comap (algebraMap F F') ≠ ⊤ := by sorry
