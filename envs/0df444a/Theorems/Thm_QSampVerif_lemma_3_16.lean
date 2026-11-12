-- Prove2me | Theorems.Thm_QSampVerif_lemma_3_16
-- name    : QSampVerif.lemma_3_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:28:28.486759+00:00
-- url     : https://prove2.me/theorems/dde54b11-25b2-4da1-a77b-bd81eb145577
-- title:
--   Lemma 3.16 — disagreements after excluding vertices: $c\ge\alpha m-\Delta|S|$
-- statement:
--   Let $G=(V,E)$ be a finite undirected multigraph whose vertex degrees are at most $\Delta$ and which has edge expansion at least $\alpha\ge0$. Let $S\subseteq V$ and let $(s_v)_{v\in V\setminus S}$ be a binary labelling. With
--
--   $$m=\min_{b\in\{0,1\}}\#\{v\notin S:s_v=b\},\qquad c=\#\{uv\in E:u,v\notin S,\ s_u\ne s_v\}$$
--
--   (edges counted with multiplicity),
--
--   $$c\ge\alpha m-\Delta|S|.\qquad(41)$$
--
--   The bound lets a set of exceptional vertices be excluded from a comparison of binary labels on an expander; it is used with the Margulis–Gabber–Galil graph in the RSP consistency tests.
--
--   **Formalization Note** The labelling is a total map $s:V\to\{0,1\}$ whose values on $S$ are never read.
--
--   Differences from the source:
--   - encoding: binary labelling (s_v)_{v∈V∖S} → a total s : V → Bool whose values on S are unused; reason: both counts read s only outside S
--   - generalization: G of maximum degree Δ → every vertex degree is at most Δ; reason: taking Δ the maximum degree gives the printed statement
--   - encoding: undirected multigraph; ∂A; edge expansion at least α → Multiset (Sym2 V) with loops counting two in the degree; the definitions of §3.8 with |A| ≤ |V|/2 compared in ℝ; reason: the conventions of p.21
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), Lemma 3.16, (41), p.22 (PDF 23); conventions §3.8, p.21 (PDF 22)

import Definitions.Def_QSampVerif_Multigraph

set_option autoImplicit false

namespace QSampVerif

/-- Chung, Cojocaru, Lee, Lin, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7),
Lemma 3.16 (Disagreements after excluding vertices), (41), p.22 (PDF 23).

Let `G = (V, E)` be an undirected multigraph of maximum degree `Δ` and edge expansion at least
`α ≥ 0`. For every `S ⊆ V` and binary labelling `(s_v)_{v ∈ V ∖ S}`, let
`m = min_{b ∈ {0,1}} #{v ∉ S : s_v = b}` and `c = #{uv ∈ E : u, v ∉ S, s_u ≠ s_v}` (with
multiplicity). Then `c ≥ α m − Δ|S|`.

**Formalization Note.** The labelling is a total map `s : V → Bool` whose values on `S` are never
read. "Maximum degree `Δ`" is the hypothesis that every degree is at most `Δ`. -/
theorem lemma_3_16 {V : Type*} [Fintype V] [DecidableEq V] (G : Multigraph V) (Δ : ℕ)
    (hΔ : ∀ v, G.degree v ≤ Δ) (α : ℝ) (hα : 0 ≤ α) (hG : G.HasEdgeExpansion α)
    (S : Finset V) (s : V → Bool) :
    α * (min (Finset.univ.filter fun v => v ∉ S ∧ s v = false).card
        (Finset.univ.filter fun v => v ∉ S ∧ s v = true).card : ℕ) - (Δ : ℝ) * S.card ≤
      (G.disagreements S s : ℝ) := by sorry

end QSampVerif
