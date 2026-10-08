-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_half_twist_hom_injective
-- name    : TarchaBraids.thm_3_15_half_twist_hom_injective
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T05:34:23.584973+00:00
-- url     : https://prove2.me/theorems/83ad2cb9-3224-4609-b337-f56cfd0b082b
-- title:
--   Teorema 3.15, step 3 — the half-twist homomorphism $B_n \to \pi_1(B_{0,n}E^2)$ is injective
-- statement:
--   This is the injectivity half of Tarcha's Teorema 3.15. Let $B_n$ be the abstract braid group,
--   presented by generators $\sigma_1,\dots,\sigma_{n-1}$ subject to
--   $$\sigma_i\sigma_j = \sigma_j\sigma_i \ (|i-j| \ge 2), \qquad
--   \sigma_i\sigma_{i+1}\sigma_i = \sigma_{i+1}\sigma_i\sigma_{i+1},$$
--   and let $\pi_1(B_{0,n}E^2,*)$ be the geometric braid group, the fundamental group of the unordered
--   configuration space of $n$ points of the plane based at the class of $(1,2,\dots,n)$. Write
--   $[\mathrm{ht}_i]$ for the class of the elementary half-twist interchanging the base points $i+1$
--   and $i+2$.
--
--   The assertion is that **any** group homomorphism
--   $$f : B_n \longrightarrow \pi_1\bigl(B_{0,n}E^2, *\bigr)$$
--   whose value on each generator is the corresponding half-twist class, $f(\sigma_{i+1}) = [\mathrm{ht}_i]$,
--   is injective. Equivalently: a word in the generators whose associated loop of configurations is
--   null-homotopic is already trivial in $B_n$, i.e. the braid relations are *all* the relations
--   satisfied by the half-twists.
--
--   In the dissertation this is the step carried out through the analysis of elementary moves on braid
--   diagrams (Figuras 3.18–3.27, pp. 57–62); the classical alternative is an induction on $n$ using the
--   exact sequence of the Fadell–Neuwirth fibration. It is the hard half of the presentation theorem:
--   the complementary facts — that the half-twists satisfy the relations, and that they generate — are
--   recorded separately as Teorema 3.15 (step 1) and Teorema 3.11.
--
--   Because the hypothesis fixes $f$ only on generators, and the generators generate $B_n$, the
--   homomorphism in question is unique; stating the lemma for an arbitrary such $f$ makes it directly
--   usable by any construction of the comparison map.
-- source:
--   Alexsander Andrey Gomes Tarcha, *Um Estudo Introdutório da Teoria de Tranças*, Dissertação (Mestrado Profissional em Matemática), IGCE, UNESP, Rio Claro, 2023, orientadora Alice Kimie Miwa Libardi, Teorema 3.15, p. 57, injectivity part of the proof, pp. 57-62 (Figuras 3.18-3.27); cf. Joan S. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82, Princeton University Press, 1974, Theorem 1.8, p. 18

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_half_twist_hom_injective (n : ℕ) (f : ArtinBraidGroup n →* GeomBraidGroup n)
    (hf : ∀ i : Fin (n - 1), f (sigma i) = halfTwistBraid n i) :
    Function.Injective f := by sorry

end TarchaBraids
