-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedGenerators_proof_05a02d77ca4f
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedGenerators_proof_05a02d77ca4f
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:00:48.992879+00:00
-- url     : https://prove2.me/theorems/56a37f06-88ca-5c2f-80c3-4169843c8a6b
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Bounded Generators proof 05a02d77ca4f: P2 M Ground Theory Heights  Heights Finite Covolume Bounded Generators proof 05a02d77ca4f
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Bounded Generators proof 05a02d77ca4f construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Bounded Generators proof 05a02d77ca4f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PBoundedGenerators.lean#L20-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PBoundedGenerators.lean#L20-L80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StBoundedGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StReducedBasisBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StArchCovolumeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StMajorantTransport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PBoundedGenerators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedGenerators_proof_05a02d77ca4f (h : HermitianForm F E W) (v : Basis ι E W)
    (hR : ReducedBasisBound.Statement) (hA : ArchCovolumeBound.Statement h v)
    (hT : MajorantTransport.Statement h v) : BoundedGenerators.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«BoundedGenerators».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedGenerators_proof_05a02d77ca4f
