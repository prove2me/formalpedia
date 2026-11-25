-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SingleBlock_measurable_toRows__be0362a1a7c9
-- name    : P2M_GlobalTheory_SingleBlock_measurable_toRows__be0362a1a7c9
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:49:42.134404+00:00
-- url     : https://prove2.me/theorems/e265fa56-73db-438e-8b18-c7ef3679322d
-- title:
--   P2 M Global Theory Single Block measurable to Rows  be0362a1a7c9: P2 M Global Theory Single Block measurable to Rows  be0362a1a7c9
-- statement:
--   The P2 M Global Theory Single Block measurable to Rows  be0362a1a7c9 construction uses the P2 M Global Theory Single Block measurable to Rows  be0362a1a7c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean#L212-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean#L212-L214

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
open GlobalTheory GlobalTheory.SingleBlock
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {r t : ℕ}
  {O : Subring F} {ϖ : F} {P : Subgroup (GL (Fin r) F)}
variable [MeasurableSpace F] [BorelSpace F]
omit [TopologicalSpace F] [IsTopologicalRing F] [BorelSpace F] [Field F]

theorem P2M_GlobalTheory_SingleBlock_measurable_toRows__be0362a1a7c9 :
    Measurable (fun x : Matrix (Fin r ⊕ Fin t) (Fin r) F => toRows₂ x) := by sorry

alias «GlobalTheory».«SingleBlock».«measurable_toRows₂» := P2M_GlobalTheory_SingleBlock_measurable_toRows__be0362a1a7c9
