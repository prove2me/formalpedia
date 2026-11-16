-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_Supplement_lemma_C_6
-- name    : SymmetricDepthHierarchy.ConstantDepth.Supplement.lemma_C_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:12:21.068885+00:00
-- url     : https://prove2.me/theorems/4a1938d3-1cf8-45fd-9ca5-59776d843210
-- title:
--   Lemma C.6 — Interpolate labelled homomorphism distinctions
-- statement:
--   Over a characteristic-zero field, let G,H be finite labelled bipartite hosts with equal corresponding side sizes, at most one label on each pair, and let N be at least either side size. Let L be any labelled bipartite graph with different side-preserving homomorphism counts into the two hosts. The conclusion supplies a multigraph F whose simple graph injects as a subgraph of the Gaifman graph of L, and one common weight vector omega. The matrices are zero padded using arbitrary specified injective indexings; the assertion holds for every such indexing.
--
--   $$
--   \operatorname{hom}(L,G)\ne\operatorname{hom}(L,H)\Rightarrow\exists F,\omega:\operatorname{hom}_{F,N}(M_G^\omega)\ne\operatorname{hom}_{F,N}(M_H^\omega).
--   $$
--
--   This result supports Theorem C.10; it retains all clauses of the source result and supplies its stated interface to the remaining companion results.
--
--   Differences from the source:
--   - encoding: finite circuits, patterns and positive matrix indices with polynomial and logarithmic resource bounds → the published circuit and pattern interfaces, finite ordinal witnesses, positive host indices and explicit eventual quantifiers; reason: finite relabelling preserves semantics and full automorphism orbits; index zero is outside X_n and no degree or total-size cap is added
--   - encoding: zero-padded weighted matrices with unspecified vertex indexing → arbitrary explicit injective row and column indexings, for each host separately; reason: the stated cardinality bounds guarantee such injections and homomorphism polynomials are unchanged by reindexing
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 44 (PDF p. 47), Lemma C.6; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Logic

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem lemma_C_6 (K : Type) [Field K] [CharZero K]
    {SLabel : Type} [Fintype SLabel] (G H L : LabelledHost SLabel)
    (hG : G.oneLabel) (hH : H.oneLabel)
    (hA : Fintype.card G.A = Fintype.card H.A) (hB : Fintype.card G.B = Fintype.card H.B)
    (N : ℕ) (hNA : Fintype.card G.A ≤ N) (hNB : Fintype.card G.B ≤ N)
    (gA : G.A ↪ Fin N) (gB : G.B ↪ Fin N) (hAi : H.A ↪ Fin N) (hBi : H.B ↪ Fin N)
    (hdiff : L.homCount G ≠ L.homCount H) :
    ∃ F : Pattern, (∃ i : (F.A ⊕ F.B) ↪ (L.A ⊕ L.B),
      ∀ u v, F.graph.Adj u v → L.graph.Adj (i u) (i v)) ∧
    ∃ ω : SLabel → K,
      MvPolynomial.eval (fun ij => G.weightedMatrix gA gB ω ij.1 ij.2) (F.homPoly K N) ≠
      MvPolynomial.eval (fun ij => H.weightedMatrix hAi hBi ω ij.1 ij.2) (F.homPoly K N) := by sorry

end SymmetricDepthHierarchy.ConstantDepth.Supplement
