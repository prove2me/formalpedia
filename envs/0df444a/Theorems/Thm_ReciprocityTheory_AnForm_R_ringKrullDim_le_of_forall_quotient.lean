-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_ringKrullDim_le_of_forall_quotient
-- name    : ReciprocityTheory.AnForm.R.ringKrullDim_le_of_forall_quotient
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:59:56.836801+00:00
-- url     : https://prove2.me/theorems/fe125b32-bc85-455d-a197-a5b9a5c36168
-- title:
--   R: ring Krull Dim le of forall quotient
-- statement:
--   The R construction uses the ring Krull Dim le of forall quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChartA.lean#L8-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChartA.lean#L8-L19

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

theorem ReciprocityTheory.AnForm.R.ringKrullDim_le_of_forall_quotient {A : Type*} [CommRing A] (d : WithBot ℕ∞)
    (h : ∀ P : Ideal A, P.IsPrime → ringKrullDim (A ⧸ P) ≤ d) : ringKrullDim A ≤ d := by sorry
