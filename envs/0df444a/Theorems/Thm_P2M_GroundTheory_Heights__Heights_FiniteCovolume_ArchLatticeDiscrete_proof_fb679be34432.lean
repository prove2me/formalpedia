-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ArchLatticeDiscrete_proof_fb679be34432
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ArchLatticeDiscrete_proof_fb679be34432
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:46:59.072191+00:00
-- url     : https://prove2.me/theorems/0444331d-3027-4749-bac7-49af9ad43a91
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Arch Lattice Discrete proof fb679be34432: P2 M Ground Theory Heights  Heights Finite Covolume Arch Lattice Discrete proof fb679be34432
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Arch Lattice Discrete proof fb679be34432 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Arch Lattice Discrete proof fb679be34432 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PArchLatticeDiscrete.lean#L32-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PArchLatticeDiscrete.lean#L32-L170

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArchLatticeDiscrete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology
open scoped Pointwise
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ArchLatticeDiscrete_proof_fb679be34432 (h : HermitianForm F E W) (v : Basis ι E W) :
    ArchLatticeDiscrete.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ArchLatticeDiscrete».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ArchLatticeDiscrete_proof_fb679be34432
