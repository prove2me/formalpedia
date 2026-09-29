-- Prove2me | Theorems.Thm_TarchaBraids_prop_3_14_three_braid_alternating_form
-- name    : TarchaBraids.prop_3_14_three_braid_alternating_form
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-18T23:47:39.77222+00:00
-- url     : https://prove2.me/theorems/adb27c1d-72ab-4347-8340-ab0f68c23663
-- title:
--   Proposição 3.14: alternating normal form for $3$-braids
-- statement:
--   Tarcha's Proposição 3.14 states that every braid on three strands can be written in the
--   alternating form
--   $$\sigma_1^{a_1}\sigma_2^{b_1}\sigma_1^{a_2}\sigma_2^{b_2}\cdots\sigma_1^{a_m}\sigma_2^{b_m},$$
--   where the exponents $a_2,\dots,a_m$ and $b_1,\dots,b_{m-1}$ are non-zero, while the first exponent
--   $a_1$ and the last exponent $b_m$ are allowed to vanish. The normalization is exactly what one
--   obtains by grouping a word in $\sigma_1^{\pm1},\sigma_2^{\pm1}$ into maximal alternating blocks: a
--   vanishing interior exponent would allow two neighbouring blocks to be merged.
--
--   The formal statement quantifies over finite sequences of exponent pairs $(a_j, b_j)$, requires the
--   product of the corresponding blocks to equal the given braid, and imposes the non-vanishing
--   conditions on all pairs except the first component of the first pair and the second component of the
--   last pair. The empty sequence is permitted and represents the identity braid.
-- source:
--   Alexsander Andrey Gomes Tarcha, *Um Estudo Introdutório da Teoria de Tranças*, Dissertação (Mestrado Profissional em Matemática), IGCE, UNESP, Rio Claro, 2023, orientadora Alice Kimie Miwa Libardi, Proposição 3.14, pp. 56–57

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

namespace TarchaBraids

open BraidsLinksMCG

theorem prop_3_14_three_braid_alternating_form (b : ArtinBraidGroup 3) :
    ∃ l : List (ℤ × ℤ),
      b = (l.map (fun p =>
            sigma (0 : Fin (3 - 1)) ^ p.1 * sigma (1 : Fin (3 - 1)) ^ p.2)).prod ∧
      (∀ p ∈ l.tail, p.1 ≠ 0) ∧ (∀ p ∈ l.dropLast, p.2 ≠ 0) := by sorry

end TarchaBraids
