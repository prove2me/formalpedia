-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CommutatorPairing_overLE___bed2ac08eb35
-- name    : P2M_GlobalTheory_CommutatorPairing_overLE___bed2ac08eb35
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:32.95745+00:00
-- url     : https://prove2.me/theorems/9348481f-de10-4da8-8dc6-117bf482468e
-- title:
--   P2 M Global Theory Commutator Pairing over LE   bed2ac08eb35: P2 M Global Theory Commutator Pairing over LE   bed2ac08eb35
-- statement:
--   The P2 M Global Theory Commutator Pairing over LE   bed2ac08eb35 construction uses the P2 M Global Theory Commutator Pairing over LE   bed2ac08eb35 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueWeilIs.lean#L216-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueWeilIs.lean#L216-L217

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CommutatorPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable {L : LB A.left} {k : ℤ}

theorem P2M_GlobalTheory_CommutatorPairing_overLE___bed2ac08eb35 {T : Over S} {V W : T.left.Opens} (h : V ≤ W) : overLE h ≫ overResι W = overResι V := by sorry

alias «GlobalTheory».«CommutatorPairing».«overLE_ι» := P2M_GlobalTheory_CommutatorPairing_overLE___bed2ac08eb35
