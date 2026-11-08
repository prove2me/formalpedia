-- Prove2me | Theorems.Thm_StreamColour_lemma_3_3
-- name    : StreamColour.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:52:45.148776+00:00
-- url     : https://prove2.me/theorems/ac032b8b-03ce-4bfa-a9c2-010404735ead
-- title:
--   Lemma 3.3 — adjacency tests on $R$ and retained edges certify any assignment
-- statement:
--   Let $R\subseteq V(G)$, and let $T$ be a test agreeing with adjacency in $G$ on every pair of distinct vertices with at least one endpoint in $R$. For $v\notin R$ let $Q(v)\subseteq[q]$ be its allowed colour set. Let $E'$ be a set of edges of $G$ containing every edge $uv$ of $G-R$ with $Q(u)\cap Q(v)\ne\emptyset$. Then for any assignment $\varphi:V(G)\to[q]$ with $\varphi(v)\in Q(v)$ for every $v\notin R$, the check that consults $T$ and $E'$ on every pair of distinct vertices of the same colour accepts if and only if $\varphi$ is proper.
--
--   This is the certificate behind the final exhaustive search: the search checks assignments using only stored data, with no second pass.
--
--   Differences from the source:
--   - encoding: "we can determine whether $\varphi$ is proper" → a function `check` of $T$, $E'$, $R$ and $\varphi$, with no access to $G$, that is true exactly when $\varphi$ is proper; reason: this is the content of "determine"; $T$ is arbitrary on pairs missing $R$
-- source:
--   Chakraborty, Chatterjee, Kundu, Mishra, Streaming Graph Colouring Meets Molloy–Reed via Kernelization (STOC 2027 submission, preprint, sha256 31a813b319e4af3fd96deb52ecd284fc2c478368ab1d9064bb951dcc884cc105), Lemma 3.3, p.22 (PDF 24)

import Mathlib
import Definitions.Def_StreamColour_Certificate

namespace StreamColour

/-- Chakraborty, Chatterjee, Kundu, Mishra, *Streaming Graph Colouring Meets Molloy–Reed via Kernelization* (STOC 2027 submission, sha256 31a813b3…), Lemma 3.3, p.22 (PDF 24).

Exact adjacency tests on pairs meeting `R`, and a retained set of original edges containing every edge of `G − R`
with intersecting allowed colour sets, determine whether an assignment respecting the allowed sets is proper.

**Formalization Note.** `T` is arbitrary on pairs missing `R`. "We can determine" is the function `check`, which is
defined from `T`, `E'` and `R` alone. -/
theorem lemma_3_3 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (q : ℕ) (R : Finset V)
    (Q : V → Finset (Fin q)) (T : V → V → Bool) (E' : Finset (Sym2 V))
    (hT : ∀ u v, u ≠ v → (u ∈ R ∨ v ∈ R) → (T u v = true ↔ G.Adj u v))
    (hE' : ∀ e ∈ E', e ∈ G.edgeSet)
    (hret : ∀ u v, G.Adj u v → u ∉ R → v ∉ R → (Q u ∩ Q v).Nonempty → s(u, v) ∈ E')
    (φ : V → Fin q) (hφ : ∀ v, v ∉ R → φ v ∈ Q v) :
    check T E' R φ = true ↔ ∀ u v, G.Adj u v → φ u ≠ φ v := by sorry

end StreamColour
