-- Prove2me | Theorems.Thm_TunnellMap_qForm_reconstructedTarget
-- name    : TunnellMap.qForm_reconstructedTarget
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:49:07.091686+00:00
-- url     : https://prove2.me/theorems/9243c3bd-b4e2-5ad6-847b-ac640c9ed372
-- title:
--   Tunnell Map: q Form reconstructed Target
-- statement:
--   The Tunnell Map construction uses the q Form reconstructed Target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/GeneratorSoundness.lean#L17-L21
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/GeneratorSoundness.lean#L17-L21

import Definitions.Def_TunnellMap_GeneratorRecovery
import Definitions.Def_TunnellMap_GeneratorSoundness
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.qForm_reconstructedTarget (E : Triple) (q : ℤ) (d : Triple) :
    qForm (reconstructedTarget E q d) =
      qForm E - 4 * q * qBilinear E d + 4 * q ^ 2 * qForm d := by sorry
