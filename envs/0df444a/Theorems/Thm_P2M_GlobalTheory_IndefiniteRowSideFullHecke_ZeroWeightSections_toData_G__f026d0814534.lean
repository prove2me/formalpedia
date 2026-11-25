-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IndefiniteRowSideFullHecke_ZeroWeightSections_toData_G__f026d0814534
-- name    : P2M_GlobalTheory_IndefiniteRowSideFullHecke_ZeroWeightSections_toData_G__f026d0814534
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:06:56.066752+00:00
-- url     : https://prove2.me/theorems/ab79202c-506a-5b21-bcda-f2d1d0b4251b
-- title:
--   P2 M Global Theory Indefinite Row Side Full Hecke Zero Weight Sections to Data G  f026d0814534: P2 M Global Theory Indefinite Row Side Full Hecke Zero Weight Sections to Data G  f026d0814534
-- statement:
--   The P2 M Global Theory Indefinite Row Side Full Hecke Zero Weight Sections to Data G  f026d0814534 construction uses the P2 M Global Theory Indefinite Row Side Full Hecke Zero Weight Sections to Data G  f026d0814534 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SectionInputData.lean#L232-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SectionInputData.lean#L232-L232

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompOrd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SectionInputData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
variable (Xo c)
variable {Xo c}
variable [Fintype (Comp Xo c)] (I : Input Xo c) (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))

theorem P2M_GlobalTheory_IndefiniteRowSideFullHecke_ZeroWeightSections_toData_G__f026d0814534 : (I.toData h δ fn yP).G2 = I.wG₂ := by sorry

alias «GlobalTheory».«IndefiniteRowSideFullHecke».«ZeroWeightSections».«toData_G₂» := P2M_GlobalTheory_IndefiniteRowSideFullHecke_ZeroWeightSections_toData_G__f026d0814534
