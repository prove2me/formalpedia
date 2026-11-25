-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ofLin_snd
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.ofLin_snd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:51:04.305535+00:00
-- url     : https://prove2.me/theorems/6d81dd5e-ab89-4f5b-b052-df90f7b63a32
-- title:
--   Chart: of Lin snd
-- statement:
--   The Chart construction uses the of Lin snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/TanLoc.lean#L74-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/TanLoc.lean#L74-L75

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
import Definitions.Def_Lemmata_MiscLemmasQ_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
variable {S : Type} [CommRing S] {B : Type} [CommRing B] [Algebra S B]
variable {A : Type} [CommRing A] [Algebra S A] (e : B →ₐ[S] A)
variable [Module B A] [IsScalarTower S B A] (hsm : ∀ (b : B) (a : A), b • a = e b * a)

theorem ReciprocityTheory.ChartRestriction.G.Chart.ofLin_snd (g : Ω[B⁄S] →ₗ[B] A) (b : B) : (ofLin e hsm g b).snd = g (KaehlerDifferential.D S B b) := by sorry
