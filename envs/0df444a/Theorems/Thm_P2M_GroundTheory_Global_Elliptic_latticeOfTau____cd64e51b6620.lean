-- Prove2me | Theorems.Thm_P2M_GroundTheory_Global_Elliptic_latticeOfTau____cd64e51b6620
-- name    : P2M_GroundTheory_Global_Elliptic_latticeOfTau____cd64e51b6620
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:56:58.012292+00:00
-- url     : https://prove2.me/theorems/0377aefe-5833-5a18-921f-a1a9450bfda1
-- title:
--   P2 M Ground Theory Global Elliptic lattice Of Tau    cd64e51b6620: P2 M Ground Theory Global Elliptic lattice Of Tau    cd64e51b6620
-- statement:
--   The P2 M Ground Theory Global Elliptic lattice Of Tau    cd64e51b6620 construction uses the P2 M Ground Theory Global Elliptic lattice Of Tau    cd64e51b6620 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/JInvariant.lean#L29-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/JInvariant.lean#L29-L29

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex UpperHalfPlane ModularForm EisensteinSeries MatrixGroups Filter Topology
open scoped PeriodPair Real
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic

theorem P2M_GroundTheory_Global_Elliptic_latticeOfTau____cd64e51b6620 (τ : ℍ) : (latticeOfTau τ).ω₁ = τ := by sorry

alias «GroundTheory».«Global».«Elliptic».«latticeOfTau_ω₁» := P2M_GroundTheory_Global_Elliptic_latticeOfTau____cd64e51b6620

attribute [defeq] P2M_GroundTheory_Global_Elliptic_latticeOfTau____cd64e51b6620
