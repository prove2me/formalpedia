-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_artin_presentation
-- name    : TarchaBraids.thm_3_15_artin_presentation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T01:23:17.49241+00:00
-- url     : https://prove2.me/theorems/50a464a5-d412-4514-b0a4-0d093e50ff0d
-- title:
--   Teorema 3.15 (Artin): $\pi_1(B_{0,n}E^2) \cong \langle \sigma_i \mid \text{braid relations}\rangle$, generator by generator
-- statement:
--   This is the capstone of the dissertation, Teorema 3.15: for $n \ge 1$ the braid group on $n$
--   strands admits the presentation
--   $$B_n = \bigl\langle \sigma_1,\dots,\sigma_{n-1} \;\bigm|\;
--   \sigma_i\sigma_j = \sigma_j\sigma_i \ (|i-j| \ge 2), \quad
--   \sigma_i\sigma_{i+1}\sigma_i = \sigma_{i+1}\sigma_i\sigma_{i+1} \bigr\rangle .$$
--   The proof in the dissertation constructs the map $\varphi$ from the presented group to the braid
--   group determined on generators by $\varphi(x_i) = [\sigma_i]$, checks that it is a well-defined
--   homomorphism, that it is surjective (Teorema 3.11) and that it is injective (the analysis of
--   elementary moves, Figuras 3.18–3.27).
--
--   Accordingly the statement formalized here is not merely that the two groups are abstractly
--   isomorphic: it asserts the existence of a group isomorphism
--   $$\varphi : B_n \xrightarrow{\ \sim\ } \pi_1\bigl(B_{0,n}E^2, *\bigr)$$
--   from the presented group onto the fundamental group of the unordered configuration space of $n$
--   points of the plane, which sends each abstract generator $\sigma_{i+1}$ to the class of the
--   elementary half-twist interchanging the base points $i+1$ and $i+2$. Fixing the isomorphism on
--   generators is what makes the presentation usable for computation with concrete braids.
--
--   The statement is asserted for every $n$; the degenerate cases $n = 0$ and $n = 1$ assert an
--   isomorphism between two trivial groups.
-- source:
--   Alexsander Andrey Gomes Tarcha, *Um Estudo Introdutório da Teoria de Tranças*, Dissertação (Mestrado Profissional em Matemática), IGCE, UNESP, Rio Claro, 2023, orientadora Alice Kimie Miwa Libardi, Teorema 3.15, p. 57 (demonstração pp. 57–62); a relação de trança impressa no enunciado do teorema contém uma errata tipográfica ("σ_i·σ_{i+1}·σ_{i+1} = σ_i·σ_{i+1}"), corrigida aqui para σ_i σ_{i+1} σ_i = σ_{i+1} σ_i σ_{i+1}, que é a relação usada na demonstração e na Proposição 3.14

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_artin_presentation (n : ℕ) :
    ∃ f : ArtinBraidGroup n ≃* GeomBraidGroup n,
      ∀ i : Fin (n - 1), f (sigma i) = halfTwistBraid n i := by sorry

end TarchaBraids
