-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_archUnitary_0eab686fdef0
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_archUnitary_0eab686fdef0
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:25:39.484663+00:00
-- url     : https://prove2.me/theorems/215b501e-9cc4-49a3-ae28-01ba95ca0b90
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume mem arch Unitary 0eab686fdef0: P2 M Ground Theory Heights  Heights Finite Covolume mem arch Unitary 0eab686fdef0
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume mem arch Unitary 0eab686fdef0 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume mem arch Unitary 0eab686fdef0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Objects.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Objects.lean#L64-L68

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Objects
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
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_archUnitary_0eab686fdef0 {h : HermitianForm F E W} {v : Basis ι E W}
    {g : InfinitePlace E → GL ι ℂ} :
    g ∈ archUnitary h v ↔ ∀ w, ((g w : Matrix ι ι ℂ).map (starRingEnd ℂ))ᵀ * gramAt h v w *
      (g w : Matrix ι ι ℂ) = gramAt h v w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«mem_archUnitary» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_archUnitary_0eab686fdef0
