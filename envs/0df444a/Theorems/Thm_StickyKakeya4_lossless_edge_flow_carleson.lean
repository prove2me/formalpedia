-- Prove2me | Theorems.Thm_StickyKakeya4_lossless_edge_flow_carleson
-- name    : StickyKakeya4.lossless_edge_flow_carleson
-- status  : Proved
-- author  : @sensei
-- created : 2026-09-26T03:07:02.051717+00:00
-- url     : https://prove2.me/theorems/6cdfd2f2-71c2-4271-b91c-0c7968b89e75
-- title:
--   Coefficient-one lossless edge-flow Carleson telescope
-- statement:
--   In a finite nested carrier forest, suppose the incoming mass at each node is the coefficient-one sum of paid mass, terminal mass, and the incoming masses of its children.  Then the sum of all paid and terminal masses is at most the total incoming mass at the roots.
--
--   This isolates the exact mass-conserving telescope needed to close the compensating stopping-tree region without logarithmic generation loss.
-- source:
--   Chenxi Cai, source manuscript https://cchx0000.github.io/papers/sticky-kakeya-contact-symplectic/sticky-kakeya-contact-symplectic.pdf, Theorem 8.56 and the cross-generation lossless edge-flow conservation in Section 9.

import Definitions.Def_sticky_kakeya4_core

namespace StickyKakeya4

theorem lossless_edge_flow_carleson
    {n : ℕ} (T : NestedCarrierTree n)
    (incoming : Fin n → ENNReal)
    (paid : Fin n → ENNReal)
    (leafMass : Fin n → ENNReal)
    (hconserve : ∀ i,
      incoming i = paid i + leafMass i +
        Finset.univ.sum (fun j : Fin n =>
          if T.parent j = some i then incoming j else 0)) :
    Finset.univ.sum (fun i : Fin n => paid i + leafMass i) ≤
      Finset.univ.sum (fun i : Fin n =>
        if T.parent i = none then incoming i else 0) := by sorry

end StickyKakeya4
