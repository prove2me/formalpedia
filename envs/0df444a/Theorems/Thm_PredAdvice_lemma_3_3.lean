-- Prove2me | Theorems.Thm_PredAdvice_lemma_3_3
-- name    : PredAdvice.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:35:44.386601+00:00
-- url     : https://prove2.me/theorems/84a68d24-de71-4714-b6a1-6333b066a2e5
-- title:
--   Lemma 3.3 — $L$ colourings and sets $R_u$ with $\sum_u |R_u| \le n^2 D 2^{-L}$
-- statement:
--   Let $G=(V,E)$ be a directed unweighted graph with $|V|=n$, let $2\le D\le n$ and $L\ge1$. There are colourings $\chi_1,\dots,\chi_L:V\to[2D]$ and sets $R_u\subseteq V$ ($u\in V$) such that
--   $$
--   \sum_{u\in V}|R_u|\le n^2D\,2^{-L}, \tag{5}
--   $$
--   for every small pair $(u,v)$ with $v\notin R_u$ every $h\in H^\circ_{u,v}$ is isolated for $(u,v)$ by at least one $\chi_j$, and $v\in R_u$ if and only if $(u,v)$ is a small unseparated pair.
--
--   Small pairs that the colourings fail to separate are few, and are covered directly by hops (or, in §4, by BFS trees).
--
--   Differences from the source:
--   - generalization: the sum bound and the isolation property → also the identity v ∈ R_u ⇔ (u, v) small and unseparated; reason: this is the definition of R_u in the proof, recalled on p.22 and used by Lemma 4.4; dropping it gives the printed lemma
--   - encoding: colours in [2D], indices in [L] → Fin (2D) shifted by one, Fin L; reason: bijective relabelling; colours enter only through equalities and the range [3D]
--   - generalization: a directed unweighted graph (simple, p.6) → Mathlib's Digraph on a finite vertex type, which may have loops; reason: loops never lie on shortest walks and change no distance; loopless digraphs on n vertices are the special case
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), Lemma 3.3, p.12, eq. (5)

import Mathlib
import Definitions.Def_PredAdvice_IsSeparated

set_option autoImplicit false

namespace PredAdvice

/-- **Lemma 3.3** (covering small unseparated pairs; Kopelowitz, Korin, Roditty, *Using Small Advice to Compress the Predecessor Matrix*, STOC 2027 submission (manuscript sha256 0ae8a68d…), §3.2, p.12). Let `2 ≤ D ≤ n = |V|`
and `L ≥ 1`. There are `L` colourings `χ_1, …, χ_L : V → [2D]` and sets `R_u ⊆ V` such that
`∑_u |R_u| ≤ n² D 2^{−L}` (eq. (5)) and, for any small pair `(u, v)` with `v ∉ R_u`, every
`h ∈ H°_{u,v}` is isolated for `(u, v)` by at least one of the colourings; and, as in the proof,
`v ∈ R_u` exactly when `(u, v)` is small and unseparated.

**Formalization Note** The last clause is the proof's definition of `R_u` ("let `v ∈ R_u` exactly
when `(u, v)` is small and unseparated"), recalled on p.22 and used by Lemma 4.4. -/
theorem lemma_3_3 :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : Digraph V) (D L : ℕ),
      2 ≤ D → D ≤ Fintype.card V → 1 ≤ L →
      ∃ (χ : Colorings V D L) (R : V → Finset V),
        ((∑ u, (R u).card : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 * D / 2 ^ L ∧
        (∀ u v : V, IsSmall G D u v → v ∉ R u →
          ∀ h ∈ Hcirc G u v, ∃ j : Fin L, Isolates G χ j u v h) ∧
        (∀ u v : V, v ∈ R u ↔ IsUnseparated G χ u v) := by sorry

end PredAdvice
