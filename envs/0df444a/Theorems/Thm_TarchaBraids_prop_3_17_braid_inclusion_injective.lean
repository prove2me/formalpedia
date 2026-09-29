-- Prove2me | Theorems.Thm_TarchaBraids_prop_3_17_braid_inclusion_injective
-- name    : TarchaBraids.prop_3_17_braid_inclusion_injective
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T01:12:56.621982+00:00
-- url     : https://prove2.me/theorems/f5149c58-a505-4cdc-ab9c-673dbb1fa720
-- title:
--   Proposição 3.17: $B_m$ embeds into $B_n$ for $m \le n$
-- statement:
--   Tarcha's Proposição 3.17 states that for $m \le n$ the map sending $\sigma_i$ to $\sigma_i$
--   for $1 \le i \le m-1$ is an injective homomorphism $B_m \to B_n$, so that $B_m$ may be regarded as a
--   subgroup of $B_n$. Geometrically it adds $n - m$ straight strands to the right of an $m$-braid, and
--   injectivity says that a braid which becomes trivial after adding trivial strands was already
--   trivial.
--
--   Formally the statement asserts the existence of a group homomorphism $f : B_m \to B_n$ which sends
--   the generator of index $i$ of $B_m$ to the generator of the same index of $B_n$ for every
--   $i \le m-2$, and which is injective. The existence and uniqueness of such an $f$ on generators is
--   the easy part (the relations of $B_m$ are among those of $B_n$); injectivity is the content.
-- source:
--   Alexsander Andrey Gomes Tarcha, *Um Estudo Introdutório da Teoria de Tranças*, Dissertação (Mestrado Profissional em Matemática), IGCE, UNESP, Rio Claro, 2023, orientadora Alice Kimie Miwa Libardi, Proposição 3.17, p. 63

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

namespace TarchaBraids

open BraidsLinksMCG

theorem prop_3_17_braid_inclusion_injective {m n : ℕ} (h : m ≤ n) :
    ∃ f : ArtinBraidGroup m →* ArtinBraidGroup n,
      (∀ i : Fin (m - 1), f (sigma i) = sigma (Fin.castLE (Nat.sub_le_sub_right h 1) i)) ∧
      Function.Injective f := by sorry

end TarchaBraids
