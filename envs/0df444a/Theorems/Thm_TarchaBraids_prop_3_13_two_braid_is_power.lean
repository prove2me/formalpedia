-- Prove2me | Theorems.Thm_TarchaBraids_prop_3_13_two_braid_is_power
-- name    : TarchaBraids.prop_3_13_two_braid_is_power
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-18T23:39:07.850935+00:00
-- url     : https://prove2.me/theorems/2fff3af7-62d4-4698-b56b-2a7a34308a49
-- title:
--   Proposição 3.13: every $2$-braid is a power of $\sigma_1$
-- statement:
--   Tarcha's Proposição 3.13 states that every braid on two strands is $\sigma_1^m$ for some
--   integer $m$. Here $B_2$ is the abstract braid group on two strands, presented by the single
--   generator $\sigma_1$ with no relations (there are no pairs of indices at distance $\ge 2$ and no
--   consecutive pairs available), so the claim is that
--   $$\forall\, b \in B_2,\ \exists\, m \in \mathbb{Z},\quad b = \sigma_1^{\,m},$$
--   the exponent $m$ being allowed to be negative or zero. Together with $\sigma_1$ having infinite
--   order this identifies $B_2$ with $\mathbb{Z}$, but only the displayed statement is asserted.
-- source:
--   Alexsander Andrey Gomes Tarcha, *Um Estudo Introdutório da Teoria de Tranças*, Dissertação (Mestrado Profissional em Matemática), IGCE, UNESP, Rio Claro, 2023, orientadora Alice Kimie Miwa Libardi, Proposição 3.13, p. 56

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

namespace TarchaBraids

open BraidsLinksMCG

theorem prop_3_13_two_braid_is_power (b : ArtinBraidGroup 2) :
    ∃ m : ℤ, b = sigma (0 : Fin (2 - 1)) ^ m := by sorry

end TarchaBraids
