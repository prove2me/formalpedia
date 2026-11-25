-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_HeckeAlgebra_HeckeAlgebraLevel_corner__idem_mul_c76622439763
-- name    : P2M_GroundTheory_Automorphic_HeckeAlgebra_HeckeAlgebraLevel_corner__idem_mul_c76622439763
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:38:27.324912+00:00
-- url     : https://prove2.me/theorems/e5a1e76a-1697-45db-84f6-e4c502e720c8
-- title:
--   P2 M Ground Theory Automorphic Hecke Algebra Hecke Algebra Level corner  idem mul c76622439763: P2 M Ground Theory Automorphic Hecke Algebra Hecke Algebra Level corner  idem mul c76622439763
-- statement:
--   The P2 M Ground Theory Automorphic Hecke Algebra Hecke Algebra Level corner  idem mul c76622439763 construction uses the P2 M Ground Theory Automorphic Hecke Algebra Hecke Algebra Level corner  idem mul c76622439763 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeIrreducible.lean#L170-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeIrreducible.lean#L170-L175

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebraLevel
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology MeasureTheory
open scoped Pointwise
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
open GroundTheory.Automorphic.HeckeAlgebra
open GroundTheory.Automorphic.HeckeAlgebra.HeckeAlgebraLevel

theorem P2M_GroundTheory_Automorphic_HeckeAlgebra_HeckeAlgebraLevel_corner__idem_mul_c76622439763 (f : HeckeAlgebra μ) :
    cornerₗ hKc hKo (idem μ hKc hKo * f) = cornerₗ hKc hKo f := by sorry

alias «GroundTheory».«Automorphic».«HeckeAlgebra».«HeckeAlgebraLevel».«cornerₗ_idem_mul» := P2M_GroundTheory_Automorphic_HeckeAlgebra_HeckeAlgebraLevel_corner__idem_mul_c76622439763
