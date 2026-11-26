-- Prove2me | Theorems.Thm_TunnellMap_reconstructedTarget_same_norm_of_tau
-- name    : TunnellMap.reconstructedTarget_same_norm_of_tau
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:17:59.109162+00:00
-- url     : https://prove2.me/theorems/7823ad0b-a38f-45c0-b725-e31a6ef2c22f
-- title:
--   Tunnell Map: reconstructed Target same norm of tau
-- statement:
--   The Tunnell Map construction uses the reconstructed Target same norm of tau property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/GeneratorSoundness.lean#L29-L35
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/GeneratorSoundness.lean#L29-L35

import Definitions.Def_TunnellMap_GeneratorRecovery
import Definitions.Def_TunnellMap_GeneratorSoundness
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.reconstructedTarget_same_norm_of_tau {E d : Triple} {A q : ℤ}
    (hnorm : dot (tau d) (tau d) = A)
    (haffine : dot (tau E) (tau d) = q * A) :
    qForm (reconstructedTarget E q d) = qForm E := by sorry
