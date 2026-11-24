-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_KH_KrullDimensionPrincipalIdeal_ringKrullDim_quotient_ne_bot
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KrullDimensionPrincipalIdeal.ringKrullDim_quotient_ne_bot
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:58.541552+00:00
-- url     : https://prove2.me/theorems/b8e15ed5-de95-4dcc-a2d5-af497b574212
-- title:
--   Krull Dimension Principal Ideal: ring Krull Dim quotient ne bot
-- statement:
--   The Krull Dimension Principal Ideal construction uses the ring Krull Dim quotient ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/KleimanNefness/AlgDimA.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/KleimanNefness/AlgDimA.lean#L31-L34

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDimSt
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_WeakRegularity_RingKrullDimQuotientAddOneLeOfLt
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_DimFormulaOfSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDimA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KrullDimensionPrincipalIdeal
open ReciprocityTheory.CA

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KrullDimensionPrincipalIdeal.ringKrullDim_quotient_ne_bot {R : Type*} [CommRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    ringKrullDim (R ⧸ I) ≠ ⊥ := by sorry
