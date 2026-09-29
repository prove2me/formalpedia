-- Prove2me | Theorems.Thm_WeierstrassProjModel_toProjective_isElliptic_map_of_isGoodPrimeFor
-- name    : WeierstrassProjModel.toProjective_isElliptic_map_of_isGoodPrimeFor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/a2fab510-2212-5fd7-9bc2-493e1ae3d6a9
-- title:
--   Good reduction at p gives an elliptic model over ℤ₍ₚ₎
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, given by its five coefficients, let $p$ be a prime number, and assume that $W$ satisfies `IsGoodPrimeFor p`, which by definition says that $p$, viewed as an integer, does not divide the discriminant $\Delta$ of $W$. Write $\mathbb{Z}_{(p)}$ for the subring `ratLocalizedAt p` of $\mathbb{Q}$ whose elements are the rationals $q$ whose denominator (in lowest terms) is coprime to $p$. The assertion is that the Weierstrass curve obtained from $W$ by base change along the structure map $\mathbb{Z} \to \mathbb{Z}_{(p)}$, and then passed to its projective Weierstrass model via `toProjective`, is elliptic, that is, the discriminant of that projective model is a unit of $\mathbb{Z}_{(p)}$.
--
--   This records that a prime not dividing the discriminant of an integral Weierstrass curve yields a genuinely elliptic Weierstrass model over the localisation $\mathbb{Z}_{(p)}$, so that the usual theory of elliptic curves applies over that base. It feeds into [`WeierstrassCurve.exists_finiteFlat_hopf_model_torsion_pow_of_isGoodPrimeFor`](thm.html#WeierstrassCurve.exists_finiteFlat_hopf_model_torsion_pow_of_isGoodPrimeFor), where a finite flat Hopf-algebra model of the $p$-power torsion is produced at a prime of good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_toProjective_isElliptic_map_of_isGoodPrimeFor.lean

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_GaloisRep_Flat
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve GaloisRep

theorem WeierstrassProjModel.toProjective_isElliptic_map_of_isGoodPrimeFor
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hgood : W.IsGoodPrimeFor p) :
    (W.map (algebraMap ℤ (ratLocalizedAt p))).toProjective.IsElliptic := by sorry
