-- Prove2me | Theorems.Thm_TarchaBraids_prop_3_16_full_twist_mem_center
-- name    : TarchaBraids.prop_3_16_full_twist_mem_center
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T00:01:22.07657+00:00
-- url     : https://prove2.me/theorems/0895e7e8-5242-446d-87a9-35cf51ea969a
-- title:
--   Proposição 3.16: the full twist $(\sigma_1\cdots\sigma_{n-1})^n$ is central
-- statement:
--   Tarcha's Proposição 3.16 states that $(\sigma_1\sigma_2\cdots\sigma_{n-1})^n$ commutes with
--   every generator $\sigma_i$, and hence lies in the centre of the braid group $B_n$. The element
--   $(\sigma_1\cdots\sigma_{n-1})^n$ is the *full twist*: geometrically, the braid obtained by rotating
--   the whole disc of base points once about its centre.
--
--   Formally, with $\Delta_{\mathrm{prod}} = \sigma_1\sigma_2\cdots\sigma_{n-1}$ the product of the
--   generators taken in increasing order of the index, the claim is
--   $$\Delta_{\mathrm{prod}}^{\,n} \in Z(B_n).$$
--   Centrality is the stronger of the two formulations in the dissertation and implies the displayed
--   commutation with each $\sigma_i$; the converse implication uses that the $\sigma_i$ generate the
--   group.
-- source:
--   Alexsander Andrey Gomes Tarcha, *Um Estudo Introdutório da Teoria de Tranças*, Dissertação (Mestrado Profissional em Matemática), IGCE, UNESP, Rio Claro, 2023, orientadora Alice Kimie Miwa Libardi, Proposição 3.16, p. 62

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

namespace TarchaBraids

open BraidsLinksMCG

theorem prop_3_16_full_twist_mem_center (n : ℕ) :
    sigmaProd n ^ n ∈ Subgroup.center (ArtinBraidGroup n) := by sorry

end TarchaBraids
