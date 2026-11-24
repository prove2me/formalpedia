-- Prove2me | Theorems.Thm_PositivityTheory_Sph_M2_GenA_tv_val
-- name    : PositivityTheory.Sph.M2.GenA.tv_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:41.312052+00:00
-- url     : https://prove2.me/theorems/63915656-a8cd-4769-9bd9-26f9f2e46a5e
-- title:
--   Gen A: tv val
-- statement:
--   The Gen A construction uses the tv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SphericalLattices/DgPerm.lean#L28-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SphericalLattices/DgPerm.lean#L28-L28

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

theorem PositivityTheory.Sph.M2.GenA.tv_val {i j : n} (h : i ≠ j) (s : K) : ((tv h s : GL n K) : Matrix n n K) = transvection i j s := by sorry
