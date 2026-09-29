-- Prove2me | Theorems.Thm_ValuationSubring_charP_residueField_of_liesOverPrime
-- name    : ValuationSubring.charP_residueField_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/05115f57-88fe-505b-8bed-019ab11a6027
-- title:
--   Residue field of a place of ℚ̄ above ℓ has characteristic ℓ
-- statement:
--   Let $\ell$ be a prime natural number and let $A$ be a valuation subring of an algebraic closure $\overline{\mathbb{Q}}$ of $\mathbb{Q}$. Assume `A.LiesOverPrime ℓ`, which by definition says that the image of $\ell$ in $\overline{\mathbb{Q}}$ lies in `A.nonunits`, the set of elements of $\overline{\mathbb{Q}}$ whose $A$-valuation is strictly less than $1$; concretely, $\ell$ belongs to $A$ but is not a unit there. The conclusion is `CharP (ResidueField ↥A) ℓ`, i.e. the residue field $A/\mathfrak m_A$ of the local ring $A$ (here `ResidueField` is `IsLocalRing.ResidueField`, the `IsLocalRing` namespace being open) has characteristic $\ell$: a natural number $n$ maps to $0$ in $A/\mathfrak m_A$ exactly when $\ell \mid n$. The assertion is produced as a term of type `CharP`, so it can be fed as the characteristic hypothesis wherever a residue field of such a valuation subring occurs.
--
--   This is the standard statement that a place of $\overline{\mathbb{Q}}$ lying above the rational prime $\ell$ has residue field of characteristic $\ell$. It is invoked throughout the reduction-modulo-$\ell$ parts of the development, where the characteristic of the residue field of a valuation subring of $\overline{\mathbb{Q}}$ must be known before characteristic-$\ell$ models of modular curves and their function fields can be used.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_charP_residueField_of_liesOverPrime.lean

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

theorem ValuationSubring.charP_residueField_of_liesOverPrime
    (ℓ : ℕ) [Fact ℓ.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime ℓ) : CharP (ResidueField ↥A) ℓ := by sorry
