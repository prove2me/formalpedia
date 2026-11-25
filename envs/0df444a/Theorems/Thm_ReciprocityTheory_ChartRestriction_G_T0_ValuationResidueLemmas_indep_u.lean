-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_indep_u
-- name    : ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.indep_u
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:28:09.135749+00:00
-- url     : https://prove2.me/theorems/99864d42-71de-409b-a51e-3a47da246375
-- title:
--   Valuation Residue Lemmas: indep u
-- statement:
--   The Valuation Residue Lemmas construction uses the indep u property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/IsUnitOfValEqZero.lean#L277-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/IsUnitOfValEqZero.lean#L277-L338

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

theorem ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.indep_u {K Ω U τ : Type} [Field K] [NumberField K] [Field Ω] [Field U] [Algebra K Ω]
    [Algebra Ω U] (w : AddValuation U (WithTop ℤ)) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (u : τ → vRing w)
    (h0 : ∀ P : MvPolynomial τ (𝓞 K), 0 < w (MvPolynomial.eval₂ ((algebraMap Ω U).comp
      ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) (fun j => (u j : U)) P) ↔
        ∀ α, P.coeff α ∈ la.asIdeal)
    (h1 : ∀ a : 𝓞 K, 0 ≤ w (((algebraMap Ω U).comp ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) a)) :
    letI _iW := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap Ω U)
    letI _io := ReciprocityTheory.MultiplicativeHeights.residueAlgebra ((vRing w).comap (algebraMap Ω U)) (algebraMap K Ω)
    letI : Algebra (ResidueField (((vRing w).comap (algebraMap Ω U)).comap (algebraMap K Ω)))
        (ResidueField (vRing w)) :=
      ((algebraMap _ (ResidueField (vRing w))).comp
        (algebraMap _ (ResidueField ((vRing w).comap (algebraMap Ω U))))).toAlgebra
    AlgebraicIndependent (ResidueField (((vRing w).comap (algebraMap Ω U)).comap (algebraMap K Ω)))
      (fun j => residue (vRing w) (u j)) := by sorry
