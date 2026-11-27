-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_N3_Pus_exists_emb
-- name    : PositivityTheory.Rg.BcB.N3.Pus.exists_emb
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:58:22.454888+00:00
-- url     : https://prove2.me/theorems/57614089-c154-5a8d-ad20-df6972e46d3e
-- title:
--   Pus: exists emb
-- statement:
--   The Pus construction uses the exists emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/SphericalEmbeddings/SigmaUniqueEqStdBlocks.lean#L13-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/SphericalEmbeddings/SigmaUniqueEqStdBlocks.lean#L13-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_SphericalEmbeddings_SigmaUniqueEqStdBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
open scoped TensorProduct
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pus

theorem PositivityTheory.Rg.BcB.N3.Pus.exists_emb (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (χ : Fin N → kˣ →* ℂˣ) :
    ∃ Ψ : (prinSeries χ).IntertwiningMap
      (multiProd (Equiv.sigmaUnique (Fin N) fun _ => Fin 1) fun i => detRep (Fin 1) (χ i)), Function.Injective Ψ := by sorry
