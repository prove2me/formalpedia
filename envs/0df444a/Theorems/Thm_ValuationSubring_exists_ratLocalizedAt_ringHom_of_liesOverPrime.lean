-- Prove2me | Theorems.Thm_ValuationSubring_exists_ratLocalizedAt_ringHom_of_liesOverPrime
-- name    : ValuationSubring.exists_ratLocalizedAt_ringHom_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/44ce1730-8450-5c48-8e35-8a23edd43e34
-- title:
--   ℤ_{(ℓ)} maps into every valuation subring over ℓ
-- statement:
--   Let $\ell$ be a natural number which is prime, and let $A$ be a valuation subring of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, an algebraic closure of $\mathbb{Q}$. Assume `A.LiesOverPrime ℓ`, that is, the image of $\ell$ in the algebraic closure is a nonunit of $A$ (it lies in $A$ and is not invertible there), so that $A$ is a valuation ring of residue characteristic $\ell$. Write $\mathbb{Z}_{(\ell)}$ for [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8), the subring of $\mathbb{Q}$ consisting of those rationals whose denominator (in lowest terms) is coprime to $\ell$. The assertion is that there exists a ring homomorphism $\rho : \mathbb{Z}_{(\ell)} \to A$ whose composite with the inclusion `A.subtype : A → AlgebraicClosure ℚ` is the structure map $\mathbb{Z}_{(\ell)} \to \mathrm{AlgebraicClosure}\ \mathbb{Q}$; equivalently, the canonical map of $\mathbb{Z}_{(\ell)}$ into the algebraic closure factors through the subring $A$, and $\rho$ is the resulting factorisation.
--
--   This records that every valuation subring of $\overline{\mathbb{Q}}$ with residue characteristic $\ell$ contains the localisation $\mathbb{Z}_{(\ell)}$, so that any such place may be regarded as a $\mathbb{Z}_{(\ell)}$-algebra. It is used throughout the reduction-theoretic part of the development, for instance when residue fields of places of modular function fields are equipped with $\mathbb{Z}_{(\ell)}$-algebra structures in the construction of characteristic-$\ell$ models of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_ratLocalizedAt_ringHom_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_CurveModelConstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicCurve IsLocalRing ModularCurve.IgusaScheme ModularCurve.CharPModel

open scoped TensorProduct

noncomputable section

theorem ValuationSubring.exists_ratLocalizedAt_ringHom_of_liesOverPrime
    (ℓ : ℕ) [Fact ℓ.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime ℓ) :
    ∃ ρ : ↥(GaloisRep.ratLocalizedAt ℓ) →+* ↥A,
      A.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ) := by sorry
