-- Prove2me | Theorems.Thm_TunnellMap_fixed_endpoint_line_unique
-- name    : TunnellMap.fixed_endpoint_line_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:23:33.076363+00:00
-- url     : https://prove2.me/theorems/d2d6c502-30dd-556c-956c-17bd699f4256
-- title:
--   Tunnell Map: fixed endpoint line unique
-- statement:
--   At a fixed endpoint and on a fixed nonzero direction, equal-norm opposite
--   endpoints are unique up to sign.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L327-L397
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L327-L397

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.fixed_endpoint_line_unique {E F₁ F₂ d : Triple} {a b : ℤ}
    (hnorm₁ : qForm F₁ = qForm E) (hnorm₂ : qForm F₂ = qForm E)
    (hd : d ≠ ⟨0, 0, 0⟩) (ha : a ≠ 0) (hb : b ≠ 0)
    (hline₁ : vadd E F₁ = vsmul a d ∨ vsub E F₁ = vsmul a d)
    (hline₂ : vadd E F₂ = vsmul b d ∨ vsub E F₂ = vsmul b d) :
    F₂ = F₁ ∨ F₂ = negTriple F₁ := by sorry
