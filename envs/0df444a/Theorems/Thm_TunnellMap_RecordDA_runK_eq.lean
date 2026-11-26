-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_runK_eq
-- name    : TunnellMap.RecordDA.runK_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:10:56.315927+00:00
-- url     : https://prove2.me/theorems/f6543ceb-b45b-56f8-ae50-45db549b8ce9
-- title:
--   Record DA: run K eq
-- statement:
--   **The fuel-driven mirror computes the integrated run.**  As soon as the
--   state reached by `runK` admits no further step, it *is* the terminal state of
--   `RecordDA.run`.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelPipeline.lean#L168-L195
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelPipeline.lean#L168-L195

import Definitions.Def_TunnellMap_KernelGenerator
import Definitions.Def_TunnellMap_ComputablePipeline
import Definitions.Def_TunnellMap_KernelPipeline
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}

theorem TunnellMap.RecordDA.runK_eq (hn : 0 ≤ n) (frames : FrameFamily n) :
    ∀ (fuel : ℕ) (E : DARun n), GenStarted E →
      (stepK frames (runK frames fuel E)).isNone = true →
      runK frames fuel E = run frames E := by sorry
