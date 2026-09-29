-- Prove2me | Theorems.Thm_PadicInt_exists_intermediateField_finiteDimensional_forall_algHom_apply_mem
-- name    : PadicInt.exists_intermediateField_finiteDimensional_forall_algHom_apply_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/e1e27172-5ee6-5e33-9c7c-68a1c05e68ff
-- title:
--   ℚ̄ₚ-points of a module-finite ℤₚ-algebra lie in one finite extension
-- statement:
--   Let $p$ be a prime and let $H$ be a commutative ring equipped with a $\mathbb{Z}_p$-algebra structure which is finite as a $\mathbb{Z}_p$-module. Then there exists an intermediate field $L$ between $\mathbb{Q}_p$ and the algebraic closure `PadicAlgCl p` such that $L$ is finite-dimensional over $\mathbb{Q}_p$ and such that, for every $\mathbb{Z}_p$-algebra homomorphism $f \colon H \to$ `PadicAlgCl p` and every element $h \in H$, the value $f(h)$ lies in $L$. The point of the shape of the conclusion is the order of the quantifiers: the single finite extension $L$ is chosen before $f$, so one and the same finite subextension of $\overline{\mathbb{Q}}_p$ contains the images of all $\mathbb{Z}_p$-algebra homomorphisms from $H$ into the algebraic closure simultaneously, not merely the image of each one separately.
--
--   This is the standard finiteness statement that the $\overline{\mathbb{Q}}_p$-valued points of a module-finite $\mathbb{Z}_p$-algebra are defined over a fixed finite extension of $\mathbb{Q}_p$, a consequence of integrality. It is used in the local analysis of residual Galois representations, where it supplies the finiteness of level needed in [`ResidualGaloisRep.unitRootInertia_trivial_and_localFlatClassesAd_le_ordinaryUnitClassesAd`](thm.html#ResidualGaloisRep.unitRootInertia_trivial_and_localFlatClassesAd_le_ordinaryUnitClassesAd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicInt_exists_intermediateField_finiteDimensional_forall_algHom_apply_mem.lean

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_GaloisRep_OrdinaryUnitClasses

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem PadicInt.exists_intermediateField_finiteDimensional_forall_algHom_apply_mem
    (p : ℕ) [Fact p.Prime] (H : Type) [CommRing H] [Algebra ℤ_[p] H] [Module.Finite ℤ_[p] H] :
    ∃ L : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] L ∧
      ∀ (f : H →ₐ[ℤ_[p]] PadicAlgCl p) (h : H), f h ∈ L := by sorry
