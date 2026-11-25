-- Prove2me | Theorems.Thm_PositivityTheory_Sph_M2_GenA_tv_mul
-- name    : PositivityTheory.Sph.M2.GenA.tv_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:03:51.314703+00:00
-- url     : https://prove2.me/theorems/6fe72b3f-2e72-4aee-a24a-91c0b4df932b
-- title:
--   Gen A: tv mul
-- statement:
--   The Gen A construction uses the tv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SphericalLattices/DgPerm.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SphericalLattices/DgPerm.lean#L30-L32

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

theorem PositivityTheory.Sph.M2.GenA.tv_mul {i j : n} (h : i ≠ j) (s t : K) : tv h s * tv h t = tv h (s + t) := by sorry
