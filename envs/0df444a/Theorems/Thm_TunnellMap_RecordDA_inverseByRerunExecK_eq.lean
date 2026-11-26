-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_inverseByRerunExecK_eq
-- name    : TunnellMap.RecordDA.inverseByRerunExecK_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:13:49.815608+00:00
-- url     : https://prove2.me/theorems/ecb4fd91-7194-5836-99b0-e1a260ea04f8
-- title:
--   Record DA: inverse By Rerun Exec K eq
-- statement:
--   The Record DA construction uses the inverse By Rerun Exec K eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelFullMap.lean#L64-L69
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelFullMap.lean#L64-L69

import Definitions.Def_TunnellMap_KernelPipeline
import Definitions.Def_TunnellMap_ComputableFullMap
import Definitions.Def_TunnellMap_KernelFullMap
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}

theorem TunnellMap.RecordDA.inverseByRerunExecK_eq (hn : 0 ≤ n) (hsq : Squarefree n)
    (fallback : BResidual n) (fuel : ℕ) (hfuel : FuelSuffices hsq fuel)
    (y : AResidual n) :
    inverseByRerunExecK hsq fallback fuel y =
      inverseByRerunExec hsq fallback y := by sorry
