-- Prove2me | Theorems.Thm_P2M_GlobalTheory_EffCartierData_existsUnique_iso_ofSec__00c3eee85ad9
-- name    : P2M_GlobalTheory_EffCartierData_existsUnique_iso_ofSec__00c3eee85ad9
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:17:51.28283+00:00
-- url     : https://prove2.me/theorems/2af03f31-2cff-5e2a-bb47-316b958d70d0
-- title:
--   P2 M Global Theory Eff Cartier Data exists Unique iso of Sec  00c3eee85ad9: P2 M Global Theory Eff Cartier Data exists Unique iso of Sec  00c3eee85ad9
-- statement:
--   The P2 M Global Theory Eff Cartier Data exists Unique iso of Sec  00c3eee85ad9 construction uses the P2 M Global Theory Eff Cartier Data exists Unique iso of Sec  00c3eee85ad9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L361-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L361-L363

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
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
open GlobalTheory
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open Cartier
open GlobalTheory.EffCartierData
variable {X Y Z : Scheme.{0}}
variable (D D' : EffCartierData X)

theorem P2M_GlobalTheory_EffCartierData_existsUnique_iso_ofSec__00c3eee85ad9 {L : LB X} (hL : L.IsLB) (s : L.Sec) (hs : IsRegularSec s) :
    ∃! w : LB.Iso (ofSec hL s hs).lb L, w.IsGen ∧ SecMaps w (ofSec hL s hs).canonical s := by sorry

alias «GlobalTheory».«EffCartierData».«existsUnique_iso_ofSec'» := P2M_GlobalTheory_EffCartierData_existsUnique_iso_ofSec__00c3eee85ad9
