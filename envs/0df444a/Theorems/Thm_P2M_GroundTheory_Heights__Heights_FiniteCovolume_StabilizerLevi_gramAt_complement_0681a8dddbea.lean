-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_gramAt_complement_0681a8dddbea
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_gramAt_complement_0681a8dddbea
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:27:19.557904+00:00
-- url     : https://prove2.me/theorems/58f4d7d5-b603-5b80-a241-554887f75d5e
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi gram At complement 0681a8dddbea: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi gram At complement 0681a8dddbea
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi gram At complement 0681a8dddbea construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi gram At complement 0681a8dddbea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviPlaces.lean#L74-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviPlaces.lean#L74-L86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviMatrices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PGramAtData
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviPlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
open NumberField GroundTheory.Automorphic Module Matrix
noncomputable section
set_option linter.unusedSectionVars false
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {h : HermitianForm F E W} {x₀ w₀ : W} {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_gramAt_complement_0681a8dddbea (v : Basis ι E W) (h' : HermitianForm F E (hypComplement h x₀ w₀))
    (hh' : ∀ x y, h'.toSesq x y = h.toSesq x y) (v' : Basis (Fin n) E (hypComplement h x₀ w₀))
    (w : InfinitePlace E) :
    gramAt h' v' w = (colMat v (fun k => (v' k : W)) w)ᴴ * gramAt h v w *
      colMat v (fun k => (v' k : W)) w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«gramAt_complement» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_gramAt_complement_0681a8dddbea
