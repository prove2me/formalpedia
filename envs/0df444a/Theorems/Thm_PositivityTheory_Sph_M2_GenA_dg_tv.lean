-- Prove2me | Theorems.Thm_PositivityTheory_Sph_M2_GenA_dg_tv
-- name    : PositivityTheory.Sph.M2.GenA.dg_tv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:03:38.269839+00:00
-- url     : https://prove2.me/theorems/947f9b50-a260-57df-9b68-e5bcb1b518fd
-- title:
--   Gen A: dg tv
-- statement:
--   The Gen A construction uses the dg tv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SphericalLattices/DgPerm.lean#L34-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SphericalLattices/DgPerm.lean#L34-L46

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

theorem PositivityTheory.Sph.M2.GenA.dg_tv {i j : n} (h : i ≠ j) (d : Kˣ) (s : K) :
    dg (Function.update 1 i d) * tv h s = tv h (d * s) * dg (Function.update 1 i d) := by sorry
