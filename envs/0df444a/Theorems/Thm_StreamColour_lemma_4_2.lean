-- Prove2me | Theorems.Thm_StreamColour_lemma_4_2
-- name    : StreamColour.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:52:56.731876+00:00
-- url     : https://prove2.me/theorems/8f8a4182-3520-47c8-a3e3-1e3d0fe1b16b
-- title:
--   Lemma 4.2 — the removal records take $O(nh\log n)$ bits, determine every edge touching $K$, and are unique
-- statement:
--   Let $G$ be an $n$-vertex graph with fixed vertex labels, and fix $h\ge1$. Apply the two reduction rules until neither applies; let $K$ be the set of removed vertices and $H=G-K$.
--
--   1. The information stored by the rules, with the removal order and each group's index, takes at most $c\,n\,h\lceil\log_2(n+1)\rceil$ bits, for an absolute constant $c$.
--   2. Given this information and any distinct $x,y$ with $\{x,y\}\cap K\ne\emptyset$, the test computed from the records alone decides whether $xy\in E(G)$.
--   3. For fixed $h$, the sets $K$ and $V(H)$ and the removal order are determined by the labelled graph $G$, and neither rule applies to $H$.
--
--   The lemma turns the kernelization into a short description of the removed part of the graph.
--
--   Differences from the source:
--   - encoding: $O(nh\log n)$ bits → an explicit count of stored labels and identifiers, at most $c\,n\,h$, at $\lceil\log_2(n+1)\rceil$ bits each; reason: $\log n$ is written with $n+1$, since $n=1$ gives $\log n=0$; a sign or rule tag is charged one identifier
--   - encoding: "uniquely determined by the labelled graph" → the records and remainder are the values of a function of $G$ and $h$, the same under any decidability instance, and no rule applies to the remainder; reason: the procedure is defined as that function; the last clause records that it has run to its end
-- source:
--   Chakraborty, Chatterjee, Kundu, Mishra, Streaming Graph Colouring Meets Molloy–Reed via Kernelization (STOC 2027 submission, preprint, sha256 31a813b319e4af3fd96deb52ecd284fc2c478368ab1d9064bb951dcc884cc105), Lemma 4.2, p.24 (PDF 26)

import Mathlib
import Definitions.Def_StreamColour_Reduction

namespace StreamColour

/-- Chakraborty, Chatterjee, Kundu, Mishra, *Streaming Graph Colouring Meets Molloy–Reed via Kernelization* (STOC 2027 submission, sha256 31a813b3…), Lemma 4.2, p.24 (PDF 26).

**Formalization Note.** The clauses, in order. (1) The stored labels and identifiers, at `⌈log₂(n+1)⌉` bits each,
take at most `c n h ⌈log₂(n+1)⌉` bits, with `c` absolute (`log n` is written with `n + 1`, since `n = 1` would give
`log n = 0`). (2) `adjOf` is computed from the records alone and agrees with `G` on distinct pairs meeting `K`.
(3) The sets and the removal order are the values of a function of `G` and `h`, the same under any decidability
instance, and the procedure has stopped: no rule applies to the remainder. -/
theorem lemma_4_2 : ∃ c : ℕ, ∀ (n h : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 1 ≤ h →
    recordBits n (removalRecords G h) ≤ c * n * h * Nat.clog 2 (n + 1) ∧
    (∀ x y, x ≠ y → (x ∉ remainder G h ∨ y ∉ remainder G h) →
      (adjOf (removalRecords G h) x y = true ↔ G.Adj x y)) ∧
    reduceStep G h (remainder G h) = none ∧
    ∀ i₁ i₂ : DecidableRel G.Adj,
      @removalRecords n G i₁ h = @removalRecords n G i₂ h ∧ @remainder n G i₁ h = @remainder n G i₂ h := by sorry

end StreamColour
