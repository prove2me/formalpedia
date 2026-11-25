-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_vecAt_coe_be48a30a30fe
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_vecAt_coe_be48a30a30fe
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:27:13.8348+00:00
-- url     : https://prove2.me/theorems/a05f7c4f-94de-541f-a67e-c8908e631fc7
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi vec At coe be48a30a30fe: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi vec At coe be48a30a30fe
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi vec At coe be48a30a30fe construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi vec At coe be48a30a30fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviPlaces.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviPlaces.lean#L41-L47

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_vecAt_coe_be48a30a30fe {W' : Submodule E W} {n : ℕ} (v : Basis ι E W) (v' : Basis (Fin n) E W') (x : W')
    (w : InfinitePlace E) :
    vecAt v (x : W) w = colMat v (fun k => (v' k : W)) w *ᵥ vecAt v' x w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«vecAt_coe» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_vecAt_coe_be48a30a30fe
