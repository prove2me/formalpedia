-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LatticePointsBelowFinite_proof_869990a84eb7
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_LatticePointsBelowFinite_proof_869990a84eb7
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:13:45.251417+00:00
-- url     : https://prove2.me/theorems/36ac3d96-9ef6-5838-8d81-85085efda63b
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Lattice Points Below Finite proof 869990a84eb7: P2 M Ground Theory Heights  Heights Finite Covolume Lattice Points Below Finite proof 869990a84eb7
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Lattice Points Below Finite proof 869990a84eb7 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Lattice Points Below Finite proof 869990a84eb7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLatticePointsBelowFinite.lean#L65-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLatticePointsBelowFinite.lean#L65-L107

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Imports
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CoerciveOfPositiveDefinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLatticePointsBelowFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix
open scoped ComplexOrder
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_LatticePointsBelowFinite_proof_869990a84eb7 (h : HermitianForm F E W) (v : Basis ι E W) :
    LatticePointsBelowFinite.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«LatticePointsBelowFinite».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_LatticePointsBelowFinite_proof_869990a84eb7
