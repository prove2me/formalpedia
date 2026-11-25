-- Prove2me | Theorems.Thm_P2M_GlobalTheory_TorsionCompare_substJ_zR__6c798f86c20b
-- name    : P2M_GlobalTheory_TorsionCompare_substJ_zR__6c798f86c20b
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:11:28.876697+00:00
-- url     : https://prove2.me/theorems/0490be4e-8b22-4af2-a9f9-428826b478e9
-- title:
--   P2 M Global Theory Torsion Compare subst J z R  6c798f86c20b: P2 M Global Theory Torsion Compare subst J z R  6c798f86c20b
-- statement:
--   The P2 M Global Theory Torsion Compare subst J z R  6c798f86c20b construction uses the P2 M Global Theory Torsion Compare subst J z R  6c798f86c20b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NotIsUnitNatCastOfIsLocalHom.lean#L123-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NotIsUnitNatCastOfIsLocalHom.lean#L123-L127

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_OriginChartMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NotIsUnitNatCastOfIsLocalHom
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
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionCompare
variable {R : Type} [CommRing R]

theorem P2M_GlobalTheory_TorsionCompare_substJ_zR__6c798f86c20b {n d : ℕ} [NeZero n] (m : ℕ) (φ : Fin d → PS R n d)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (q : Fin 1 × Fin d) :
    substJ m φ hφ (zR m q) = jetOfSeries m (φ q.2) := by sorry

alias «GlobalTheory».«TorsionCompare».«substJ_zR'» := P2M_GlobalTheory_TorsionCompare_substJ_zR__6c798f86c20b
