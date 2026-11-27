-- Prove2me | Theorems.Thm_P2M_GlobalTheory_WachLettersCompare__D_fixed_4a0839ac6157
-- name    : P2M_GlobalTheory_WachLettersCompare__D_fixed_4a0839ac6157
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:06:25.792165+00:00
-- url     : https://prove2.me/theorems/25c38416-2c28-5150-94ee-edf12d884190
-- title:
--   P2 M Global Theory Wach Letters Compare  D fixed 4a0839ac6157: P2 M Global Theory Wach Letters Compare  D fixed 4a0839ac6157
-- statement:
--   The P2 M Global Theory Wach Letters Compare  D fixed 4a0839ac6157 construction uses the P2 M Global Theory Wach Letters Compare  D fixed 4a0839ac6157 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LetterSandwichOfFrobMatrices.lean#L104-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LetterSandwichOfFrobMatrices.lean#L104-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_LettersFreeOfRank
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_WachLettersFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LetterSandwichOfFrobMatrices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.WachLettersCompare
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)
attribute [local instance] letterModule
variable {W T}

theorem P2M_GlobalTheory_WachLettersCompare__D_fixed_4a0839ac6157 (i : ZMod n) {x : W.DD T} (hx : x ∈ W.Nl T (i - 1)) :
    (letE i : LetA O n) • W.φD T x = W.φD T x := by sorry

alias «GlobalTheory».«WachLettersCompare».«φD_fixed» := P2M_GlobalTheory_WachLettersCompare__D_fixed_4a0839ac6157
