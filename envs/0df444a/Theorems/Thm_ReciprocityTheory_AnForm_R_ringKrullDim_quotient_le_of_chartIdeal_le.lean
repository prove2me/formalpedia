-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_ringKrullDim_quotient_le_of_chartIdeal_le
-- name    : ReciprocityTheory.AnForm.R.ringKrullDim_quotient_le_of_chartIdeal_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:47:36.604372+00:00
-- url     : https://prove2.me/theorems/81e42bf1-9c1b-5e9b-8a60-5f9e0530fe78
-- title:
--   R: ring Krull Dim quotient le of chart Ideal le
-- statement:
--   The R construction uses the ring Krull Dim quotient le of chart Ideal le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChartA.lean#L101-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChartA.lean#L101-L217

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial Algebra
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.AnForm.R.ringKrullDim_quotient_le_of_chartIdeal_le {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hP : IsMultiHomogIdeal P) (e : ℕ)
    (hdim : ∀ Q ∈ P.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞))
    (p : (k : K) → ι k) (𝔮 : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [𝔮.IsPrime]
    (h𝔮 : chartIdeal P p ≤ 𝔮) :
    ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) ≤ e := by sorry
