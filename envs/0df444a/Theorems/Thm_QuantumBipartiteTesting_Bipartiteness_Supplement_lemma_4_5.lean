-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_Supplement_lemma_4_5
-- name    : QuantumBipartiteTesting.Bipartiteness.Supplement.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:14:50.851675+00:00
-- url     : https://prove2.me/theorems/6634ad7a-642a-41b6-b5b4-6316fe6b2a15
-- title:
--   Lemma 4.5 — Replacement graph preserves expansion
-- statement:
--   For any $\beta,h_0>0$ there is $\alpha>0$, depending only on these parameters, with the following property. Let $H$ be any consistent colored matching multigraph on $n$ vertices with $c>0$ colors and
--   $$|e_H(U,U^c)|\ge\beta c\min\{|U|,n-|U|\}\quad\text{for every }U.$$
--   For every fixed simple cubic cloud $J$ with edge expansion $h_0$, the actual replacement graph $R_J(H)$ has vertex expansion at least $\alpha$. Any fixed bijective labeling of its $nc$ vertices is allowed. This transfers the YES expansion promise to maximum-degree-four graphs.
--
--   Differences from the source:
--   - encoding: replacement vertices (u,j) and a positive constant depending only on beta,h0 → any fixed bijective labeling of Fin (n*c), with alpha quantified before n,c,J,H; reason: this makes the stated uniformity and free vertex labeling explicit
--   - generalization: the section constructs clouds at logarithmic color counts from one fixed expanding cubic family → every positive color count and every simple cubic cloud with the stated edge expansion; reason: the A.8 cut argument depends only on beta and h0, so the statement includes every cloud and color count used in the source
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf, Lemma 4.5, printed page = PDF page 23; proof p.38

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Supplement_Unsigned

namespace QuantumBipartiteTesting.Bipartiteness.Supplement
open Finset

theorem lemma_4_5 (β h₀ : ℝ) (hβ : 0 < β) (hh : 0 < h₀) :
    ∃ α : ℝ, 0 < α ∧ ∀ n c : ℕ, 0 < c →
      ∀ e : Fin (n*c) ≃ Fin n × Fin c, ∀ J : Finset (Edge c), Cloud h₀ J →
      ∀ H : Finset (ColoredEdge n c), Consistent H → ColoredExpansion β H →
        VertexExpander α (Replacement e J H) := by sorry

end QuantumBipartiteTesting.Bipartiteness.Supplement
