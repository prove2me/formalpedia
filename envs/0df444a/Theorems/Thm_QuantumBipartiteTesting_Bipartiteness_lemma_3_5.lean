-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_3_5
-- name    : QuantumBipartiteTesting.Bipartiteness.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:12:42.070304+00:00
-- url     : https://prove2.me/theorems/3019f858-bc26-4d74-ac88-35c3710d371f
-- title:
--   Lemma 3.5 — signing probabilities and forest cancellation
-- statement:
--   Let $F$ be a consistent colored multigraph with $v$ incident vertices, $e$ distinct edges and $c$ connected components, and fix every edge sign. Then
--   $$s_{\rm no}=2^{-e},\qquad s_{\rm yes}=\begin{cases}2^{-(v-c)},&\text{if the signing is balanced},\\0,&\text{otherwise}.\end{cases}$$
--   If $F$ is a forest, the two probabilities agree for every signing. The probabilities are the finite averages of actual independent edge bits or vertex bits, rather than values stipulated by this formula. This is the cancellation used in the formal acceptance gap.
--
--   Differences from the source:
--   - encoding: vertices [N], distinct undirected edges and color-labeled parallel edges → Fin N; oriented unordered pairs; color included in each edge identifier; reason: bijections relabel vertices; differently colored parallel constraints remain distinct
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), Lemma 3.5, PDF = printed page 15. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction

namespace QuantumBipartiteTesting.Bipartiteness
open Finset
attribute [local instance] Classical.propDecidable

theorem lemma_3_5 {N colors : ℕ} (F : Finset (ColoredEdge N colors)) (hF : Consistent F)
    (b : ColoredEdge N colors → Bool) :
    SignProbNo F b = (2 : ℝ) ^ (-(F.card : ℤ)) ∧
    SignProbYes F b = (if Balanced F b then
      (2 : ℝ) ^ (-((Vertices F).card : ℤ) + (Components F).card) else 0) ∧
    (Forest F → SignProbYes F b = SignProbNo F b) := by sorry

end QuantumBipartiteTesting.Bipartiteness
