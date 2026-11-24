-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CuspCentre_cc_mul__aa1f1980283c
-- name    : P2M_GlobalTheory_CuspCentre_cc_mul__aa1f1980283c
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:36:45.416349+00:00
-- url     : https://prove2.me/theorems/ffe6d418-d2b7-4ca4-9851-7f394b79d54a
-- title:
--   P2 M Global Theory Cusp Centre cc mul  aa1f1980283c: P2 M Global Theory Cusp Centre cc mul  aa1f1980283c
-- statement:
--   The P2 M Global Theory Cusp Centre cc mul  aa1f1980283c construction uses the P2 M Global Theory Cusp Centre cc mul  aa1f1980283c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ZMatEInjective.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ZMatEInjective.lean#L20-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ZMatEInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.CuspCentre
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem P2M_GlobalTheory_CuspCentre_cc_mul__aa1f1980283c (x y : E) : cc (x * y) = cc x * cc y := by sorry

alias «GlobalTheory».«CuspCentre».«cc_mul'» := P2M_GlobalTheory_CuspCentre_cc_mul__aa1f1980283c
