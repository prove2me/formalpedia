-- Prove2me | Theorems.Thm_PelagicFF_transcript_rectangle
-- name    : PelagicFF.transcript_rectangle
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:55:00.925533+00:00
-- url     : https://prove2.me/theorems/770807a8-1f28-476c-94e8-4f1d2cdab6a3
-- title:
--   §4.2.2, p.30 — at most $2^c$ transcripts, each a combinatorial rectangle
-- statement:
--   Let $\pi$ be a deterministic two-party protocol of depth $c$ with input sets $A$, $B$. Then
--
--   1. $\pi$ has at most $2^c$ distinct transcripts: $\big|\{\pi(a,b): a\in A,\ b\in B\}\big|\le 2^c$;
--   2. for every input pair $(a_0,b_0)$, the set $R_\tau=\{(a,b):\pi(a,b)=\pi(a_0,b_0)\}$ of inputs producing the transcript $\tau=\pi(a_0,b_0)$ is a combinatorial rectangle $A_\tau\times B_\tau$.
--
--   These two facts start the lower bound: conditioned on a transcript, Alice's and Bob's inputs stay independent and uniform on $A_\tau$, $B_\tau$.
--
--   **Formalization Note** Transcripts, rectangles and $R_\tau$ are the published `GrossmanInevitable.Intersection` definitions over `OneOfManyCC.Protocol`; the count is an extended-natural cardinality, so no finiteness is assumed.
--
--   Differences from the source:
--   - generalization: the c-bit protocol of the proof, on inputs {−1,1}^N × {−1,1}^N → every deterministic protocol, with arbitrary input and output types, of depth c; reason: the inputs of the proof are a special case
--   - encoding: "at most 2^c transcript leaves"; "for each nonempty leaf τ" → the set of transcripts realised by some input has cardinality ≤ 2^depth; for each input pair (a₀, b₀), the inputs with the same transcript; reason: a nonempty leaf is one reached by some input; same objects
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), §4.2.2, p.30

import Mathlib
import Definitions.Def_OneOfManyCC_Protocol
import Definitions.Def_GrossmanInevitable_Intersection_Transcript

open GrossmanInevitable.Intersection

namespace PelagicFF

/-- **Transcripts of a deterministic protocol (§4.2.2, p.30).** A deterministic protocol of depth
`c` has at most `2^c` distinct transcripts, and for each transcript `τ` the set of inputs producing
`τ` is a combinatorial rectangle `A_τ × B_τ`.

arXiv:2610.05585 (held version, sha256 4564aef3…), §4.2.2, p.30: "The protocol has at most 2^c
transcript leaves. For each nonempty leaf τ, the inputs producing τ form a combinatorial rectangle
A_τ × B_τ ⊆ {−1,1}^N × {−1,1}^N."

**Formalization Note.** Stated for every deterministic protocol (published `OneOfManyCC.Protocol`)
with arbitrary input and output types; transcripts, rectangles and `R_τ` are the published
`GrossmanInevitable.Intersection` notions. The count is an `ℕ∞`-cardinality, so no finiteness
assumption is hidden. -/
theorem transcript_rectangle {A B O : Type} (π : OneOfManyCC.Protocol A B O) :
    (Set.range (fun p : A × B => transcript π p.1 p.2)).encard ≤ (2 : ℕ∞) ^ π.depth ∧
    ∀ (a₀ : A) (b₀ : B), IsRectangle (transcriptRect π a₀ b₀) := by sorry

end PelagicFF
