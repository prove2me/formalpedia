-- Prove2me | Theorems.Thm_QMA2ClassicalSep_Main_lemma_6_9
-- name    : QMA2ClassicalSep.Main.lemma_6_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:40.156312+00:00
-- url     : https://prove2.me/theorems/5f74a679-832d-4249-9877-e1df0122cd50
-- title:
--   Lemma 6.9 — exact properties of completion: $\|W\xi\|\le\|\xi\|$ and $Z_-W=WZ_+$
-- statement:
--   Let $k\ge2$. The completion map $W:\mathrm{Rec}_+\to\mathrm{Rec}_-$ of Equation (13) satisfies:
--
--   1. $\|W\xi\|\le\|\xi\|$ for every $\xi\in\mathrm{Rec}_+$;
--   2. $$Z_-W=WZ_+ ,$$ as operators from $\mathrm{Rec}_+\otimes(\text{query register})$ to $\mathrm{Rec}_-\otimes(\text{query register})$, with $W$ acting as $W\otimes I$.
--
--   Completion therefore commutes exactly with the part of a query that reads stored entries and signs.
--
--   Differences from the source:
--   - encoding: Z₋W = WZ₊ → Z₋ (W ⊗ I_query) = (W ⊗ I_query) Z₊; reason: Z_± act on records ⊗ query register; W acts on the record factor
-- source:
--   Sabee Grewal, Saachi Mutreja, Kabir Tomer, A classical oracle separation between QMA and QMA(2), STOC 2027 submission #618 (October 2026), SHA-256 79883d9d08b98b41b1bb600a6644f3f578ecb803702383a9f2a58d5bc7dacedf, pp. 35–36, Lemma 6.9

import Definitions.Def_QMA2ClassicalSep_Main_Completion

namespace QMA2ClassicalSep.Main

theorem lemma_6_9 (k : ℕ) (hk : 2 ≤ k) :
    (∀ ξ : YRec k → ℂ, vnorm ((compW (k := k)).mulVec ξ) ≤ vnorm ξ) ∧
    zN (k := k) * tensorId (QReg k (3 * k)) (compW (k := k)) =
      tensorId (QReg k (3 * k)) (compW (k := k)) * zY (k := k) := by sorry

end QMA2ClassicalSep.Main
