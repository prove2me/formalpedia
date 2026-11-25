-- Prove2me | Theorems.Thm_P2M_GlobalTheory_RootEx_ConjVol_integral_conj_colE__c90594e99930
-- name    : P2M_GlobalTheory_RootEx_ConjVol_integral_conj_colE__c90594e99930
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:08:59.774568+00:00
-- url     : https://prove2.me/theorems/0bd55dff-f7e5-4fda-b930-4d74b6ed2651
-- title:
--   P2 M Global Theory Root Ex Conj Vol integral conj col E  c90594e99930: P2 M Global Theory Root Ex Conj Vol integral conj col E  c90594e99930
-- statement:
--   The P2 M Global Theory Root Ex Conj Vol integral conj col E  c90594e99930 construction uses the P2 M Global Theory Root Ex Conj Vol integral conj col E  c90594e99930 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemNormalizerOfTri.lean#L127-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemNormalizerOfTri.lean#L127-L154

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemNormalizerOfTri
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open scoped NNReal
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.ConjVol
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]

theorem P2M_GlobalTheory_RootEx_ConjVol_integral_conj_colE__c90594e99930 (p : ℕ) (β : n → k) (f : GL (n ⊕ Fin c) k → ℂ) :
    ∫ u : N k n c p, f (colE c p β * (u : GL (n ⊕ Fin c) k) * (colE c p β)⁻¹) ∂(volN ν n c p) =
      ∫ u : N k n c p, f u ∂(volN ν n c p) := by sorry

alias «GlobalTheory».«RootEx».«ConjVol».«integral_conj_colE'» := P2M_GlobalTheory_RootEx_ConjVol_integral_conj_colE__c90594e99930
