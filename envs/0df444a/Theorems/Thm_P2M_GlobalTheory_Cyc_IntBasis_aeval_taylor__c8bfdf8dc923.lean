-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Cyc_IntBasis_aeval_taylor__c8bfdf8dc923
-- name    : P2M_GlobalTheory_Cyc_IntBasis_aeval_taylor__c8bfdf8dc923
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:07:01.819068+00:00
-- url     : https://prove2.me/theorems/40813070-4ed0-48ff-9a45-75018ccd59c8
-- title:
--   P2 M Global Theory Cyc Int Basis aeval taylor  c8bfdf8dc923: P2 M Global Theory Cyc Int Basis aeval taylor  c8bfdf8dc923
-- statement:
--   The P2 M Global Theory Cyc Int Basis aeval taylor  c8bfdf8dc923 construction uses the P2 M Global Theory Cyc Int Basis aeval taylor  c8bfdf8dc923 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegersEqSumZetaPow.lean#L178-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegersEqSumZetaPow.lean#L178-L181

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMemCyclotomicLayerPrimeRpowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.IntBasis
variable {l : ℕ} [Fact l.Prime]

theorem P2M_GlobalTheory_Cyc_IntBasis_aeval_taylor__c8bfdf8dc923 {R : Type} [CommRing R] [Algebra R (Om l)] (p : R[X]) (r : R) (w : Om l) :
    aeval w (taylor r p) = aeval (w + algebraMap R _ r) p := by sorry

alias «GlobalTheory».«Cyc».«IntBasis».«aeval_taylor'» := P2M_GlobalTheory_Cyc_IntBasis_aeval_taylor__c8bfdf8dc923
