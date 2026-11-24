-- Prove2me | Theorems.Thm_PositivityTheory_Sph_M2_GenA_dg_val
-- name    : PositivityTheory.Sph.M2.GenA.dg_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:19.480913+00:00
-- url     : https://prove2.me/theorems/a7ca42bc-2b64-4d6a-b7f9-19c1d0ce4455
-- title:
--   Gen A: dg val
-- statement:
--   The Gen A construction uses the dg val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SphericalLattices/DgPerm.lean#L22-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SphericalLattices/DgPerm.lean#L22-L22

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SphericalLattices_DgPerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Sph PositivityTheory.Sph.M2 PositivityTheory.Sph.M2.GenA
open Matrix
variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]

theorem PositivityTheory.Sph.M2.GenA.dg_val (D : n → Kˣ) : ((dg D : GL n K) : Matrix n n K) = diagonal fun i => (D i : K) := by sorry
