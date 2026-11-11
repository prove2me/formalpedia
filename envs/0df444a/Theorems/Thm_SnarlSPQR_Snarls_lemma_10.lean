-- Prove2me | Theorems.Thm_SnarlSPQR_Snarls_lemma_10
-- name    : SnarlSPQR.Snarls.lemma_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:30:44.399062+00:00
-- url     : https://prove2.me/theorems/ef4bd838-855f-4694-a776-809c7b369586
-- title:
--   Lemma 10 — no snarl joins vertex-sides of two distinct sign-cut graphs
-- statement:
--   Let $G$ be a loopless bidirected graph, let $F_1\neq F_2$ be sign-cut graphs of $G$, let $u\alpha$ be a vertex-side of $F_1$ (it lies on an edge of $F_1$) and let $v\beta$ be a vertex-side of $F_2$. Then
--   $$\{u\alpha,v\beta\}\ \text{is not a snarl of } G.$$
--   Every snarl therefore has both vertex-sides in a single sign-cut graph. This is the first step towards Lemma 11.
--
--   Differences from the source:
--   - reading: G a bidirected graph → G : BiGraph V with G.Valid (every endpoint of an edge is a vertex, no loops); the edges form a Finset, so there are no parallel edges; reason: standing assumptions of §3 (no parallel edges, p. 9) and §5.1 (no loops, p. 28); splitting is only defined for loopless graphs
-- source:
--   Sena, Politov, Moumard, Cairo, Rizzi, Cáceres, Schmidt, Harviainen, Tomescu, Identifying bubble-like subgraphs in linear-time via a unified SPQR-tree framework, arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), p. 30, Lemma 10

import Mathlib
import Definitions.Def_SnarlSPQR_Snarls_SignCut

namespace SnarlSPQR.Snarls

/-- Lemma 10 (p. 30): a vertex-side of one sign-cut graph and a vertex-side of another never form
a snarl of `G`. -/
theorem lemma_10 {V : Type} (G F₁ F₂ : BiGraph V) (hG : G.Valid)
    (hF₁ : G.IsSignCut F₁) (hF₂ : G.IsSignCut F₂) (hne : F₁ ≠ F₂)
    (a b : V × Sign) (ha : a ∈ F₁.sides) (hb : b ∈ F₂.sides) :
    ¬ G.Snarl a b := by sorry

end SnarlSPQR.Snarls
