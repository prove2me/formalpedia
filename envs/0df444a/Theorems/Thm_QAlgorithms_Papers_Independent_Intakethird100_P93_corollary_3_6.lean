-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P93_corollary_3_6
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P93.corollary_3_6
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:37:29.442854+00:00
-- url     : https://prove2.me/theorems/f2d5584f-0ca9-4059-b196-4a4802d66690
-- title:
--   Bibundle triviality is unit type plus trivial kernel reduction
-- statement:
--   Let $t:G\to H$ be a topological crossed module, with continuous action $\alpha:H\to\operatorname{Aut}(G)$. Thus $t(\alpha(h)g)=ht(g)h^{-1}$ and $\alpha(t(g))k=gkg^{-1}$. Put $G_1=\ker t$ and give both $G/G_1$ and $H/t(G)$ their quotient topologies. Assume their quotient projections admit continuous local sections. All actions, structure maps and isomorphisms below are continuous, all principal bundles are locally trivial, and a bispace has a nonempty principal homogeneous underlying right space.
--
--   Let $P\to M$ be an $(H,G)$-bibundle with structure map $\psi$, and put $P_1=\psi^{-1}(1)$. Then
--
--   $$
--   P\text{ is trivial as an }(H,G)\text{-bibundle}
--   \iff \operatorname{Type}(P)\equiv1\ \text{and }P_1\text{ is trivial as a }G_1\text{-bundle}.
--   $$
--
--   Triviality on the left means an equivariant homeomorphism over $M$ with $M\times G$ preserving the structure map $t$ on the second coordinate. Triviality of $P_1$ means an equivariant homeomorphism over $M$ with $M\times G_1$; it is not assumed to be a principal bundle before unit type is known. This tests bibundle triviality with its structure map retained.
-- source:
--   On the existence of bibundles, arXiv:1102.4388v2, PDF p. 11, Corollary 3.6

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P93

namespace QAlgorithms.Papers.Independent.Intakethird100.P93

universe u

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable (C : CrossedModule G H)

/-- Corollary 3.6, PDF p.11. 'Trivial' preserves the bibundle structure.
The preceding text's (1,t(G)) is corrected to (1,ker(t)), as required by
Lemma 2.10 and the reconstruction on the same page. The empty base is allowed. -/
theorem corollary_3_6 {M P : Type u} [TopologicalSpace M] [TopologicalSpace P]
    (B : Bibundle C M P) :
    IsTrivialBibundle C B ↔ HasUnitType C B ∧ IsTrivialUnitLevel C B := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P93
