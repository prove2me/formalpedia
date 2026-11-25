-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_exists_val_coeff
-- name    : ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.exists_val_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:20.954801+00:00
-- url     : https://prove2.me/theorems/78f2e820-90d2-4ce2-add5-7ec03bc11a3c
-- title:
--   Valuation Residue Lemmas: exists val coeff
-- statement:
--   The Valuation Residue Lemmas construction uses the exists val coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/IsUnitOfValEqZero.lean#L175-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/IsUnitOfValEqZero.lean#L175-L234

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas

theorem ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.exists_val_coeff {Ω U σ : Type} [Field Ω] [Field U] [Algebra Ω U]
    (w : AddValuation U (WithTop ℤ)) (t : σ → U) (ht : ∀ s, t s ∈ vRing w)
    (hind : letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap Ω U)
      AlgebraicIndependent (ResidueField ((vRing w).comap (algebraMap Ω U)))
        (fun s => residue (vRing w) ⟨t s, ht s⟩))
    (P : MvPolynomial σ Ω) (hP : P ≠ 0) :
    ∃ c : Ω, c ≠ 0 ∧ w (MvPolynomial.aeval t P) = w (algebraMap Ω U c) := by sorry
