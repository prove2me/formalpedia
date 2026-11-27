-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IndefiniteRowSideFullHecke_ZeroWeightSections_toData_F__1564f8e39eb7
-- name    : P2M_GlobalTheory_IndefiniteRowSideFullHecke_ZeroWeightSections_toData_F__1564f8e39eb7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:06:07.016255+00:00
-- url     : https://prove2.me/theorems/be5b424e-b3d9-5603-8ff2-8e0eff09df8e
-- title:
--   P2 M Global Theory Indefinite Row Side Full Hecke Zero Weight Sections to Data F  1564f8e39eb7: P2 M Global Theory Indefinite Row Side Full Hecke Zero Weight Sections to Data F  1564f8e39eb7
-- statement:
--   The P2 M Global Theory Indefinite Row Side Full Hecke Zero Weight Sections to Data F  1564f8e39eb7 construction uses the P2 M Global Theory Indefinite Row Side Full Hecke Zero Weight Sections to Data F  1564f8e39eb7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SectionInputData.lean#L231-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SectionInputData.lean#L231-L231

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

theorem P2M_GlobalTheory_IndefiniteRowSideFullHecke_ZeroWeightSections_toData_F__1564f8e39eb7 : (I.toData h δ fn yP).F0 = I.wF₀ := by sorry

alias «GlobalTheory».«IndefiniteRowSideFullHecke».«ZeroWeightSections».«toData_F₀» := P2M_GlobalTheory_IndefiniteRowSideFullHecke_ZeroWeightSections_toData_F__1564f8e39eb7
