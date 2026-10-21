-- Prove2me | Theorems.Thm_PayAsBid_SoftReserve_lemma_3
-- name    : PayAsBid.SoftReserve.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:56.000016+00:00
-- url     : https://prove2.me/theorems/ca83e0b7-15eb-45bc-a422-22ae27d478b8
-- title:
--   Lemma 3, p. A2 — in an optimal solution of Problem (8), b∗_L ≤ b∗_H
-- statement:
--   Consider Model 2 with two-point costs under the standing assumptions. Let $(q^*,r^*,b^*_L,b^*_H)$ be an optimal solution of Problem (8). Then
--
--   $$b^*_L\le b^*_H.$$
--
--   In every optimal equitable mechanism, low-cost suppliers price no higher than high-cost suppliers. This ordering is what lets the soft reserve sit at $b^*_L$ below the hard reserve $b^*_H$.
-- source:
--   Choi, Saban & Weintraub, The Design of Optimal Pay-as-Bid Procurement Mechanisms, SSRN preprint 3785023 (version of 2022-12-08), p. A2 (PDF 35), Lemma 3

import Mathlib
import Definitions.Def_PayAsBid_SoftReserve_Model

namespace PayAsBid.SoftReserve

theorem lemma_3 {n : ℕ} (P : Params n) (hP : P.Standing)
    (q : AssortFn n) (r bL bH : ℝ) (hopt : IsOptimal8 P q r bL bH) :
    bL ≤ bH := by sorry

end PayAsBid.SoftReserve
