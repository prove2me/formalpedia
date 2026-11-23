-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_val_eval_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.val_eval_eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:48.52583+00:00
-- url     : https://prove2.me/theorems/027df1aa-99ad-4294-bba2-ea90f0ac2fa2
-- title:
--   Valuation Residue Lemmas: val eval eq zero
-- statement:
--   The Valuation Residue Lemmas construction uses the val eval eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/IsUnitOfValEqZero.lean#L106-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/IsUnitOfValEqZero.lean#L106-L173

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

theorem ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.val_eval_eq_zero {Ω U σ : Type} [Field Ω] [Field U] [Algebra Ω U]
    (w : AddValuation U (WithTop ℤ)) (t : σ → U) (ht : ∀ s, t s ∈ vRing w)
    (hind : letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap Ω U)
      AlgebraicIndependent (ResidueField ((vRing w).comap (algebraMap Ω U)))
        (fun s => residue (vRing w) ⟨t s, ht s⟩))
    (P : MvPolynomial σ Ω) (hP : ∀ β, 0 ≤ w (algebraMap Ω U (P.coeff β))) (α : σ →₀ ℕ)
    (h1 : P.coeff α = 1) :
    w (MvPolynomial.aeval t P) = 0 := by sorry
