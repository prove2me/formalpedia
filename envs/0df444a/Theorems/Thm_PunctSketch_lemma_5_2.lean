-- Prove2me | Theorems.Thm_PunctSketch_lemma_5_2
-- name    : PunctSketch.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:47:00.214531+00:00
-- url     : https://prove2.me/theorems/43e59c8c-08f2-4b97-a29b-459d42921be9
-- title:
--   Lemma 5.2, p.17 — the Borůvka process fails with probability at most $n^{-(k+3)}$
-- statement:
--   Let $a\ge0$. There is $n_0$ such that for $n\ge n_0$, $1\le k<n$, any graph $G$ and any $F$ with $|F|<k$: if a procedure with coins on a finite space is a boundary sampling oracle for $G\setminus F$ with failure $e^{-2k}$ and hallucination $n^{-(k+5+a)}$, then with independent uniform coins in each of the $R=10(a+1)\lceil\log_{4/3}n\rceil$ rounds,
--   $$\Pr[\text{the process fails to complete or a query returns a pair outside the boundary of its blob}]\le n^{-(k+3+a)}.$$
--   The case $a=0$ is the printed lemma. The blobs of round $r$ depend on earlier rounds only, whose coins are independent of those of round $r$.
--
--   Differences from the source:
--   - generalization: the Lemma 5.1 bound n^{−(k+5)}, R = 10g, conclusion n^{−(k+3)} → parameter a, with n^{−(k+5+a)}, R = 10(a+1)g, conclusion n^{−(k+3+a)}; reason: a = 0 is the printed statement
--   - generalization: the sampler of Lemma 5.1 → any boundary sampling oracle with those two probabilities, on any finite coin space; reason: "With the failure and hallucination probabilities of the boundary sampler oracle bounded as in Lemma 5.1" is all the proof uses
--   - reading: n large (standing assumption, p.4) → ∃ n₀ depending on a only; reason: the union bound over at most nR sampler calls needs R small against n
--   - reading: "It could hallucinate an edge of G ⧵ F" → some query at a blob C returned a pair outside ∂_{−F}C; reason: this is the event that Definition 2.1 bounds and the union bound of the proof sums over
--   - encoding: Borůvka-style region growing → query at the blob of each vertex outside F, then add a returned pair when it joins two components; reason: blobs repeat for their several vertices, with the same reply since the coins are the same
--   - encoding: vertices [n] = {1, …, n} → Fin n, zero-indexed; reason: Lean convention; same instances
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), Lemma 5.2, p.17 (PDF p.18)

import Mathlib
import Definitions.Def_PunctSketch_BoruvkaFails
import Definitions.Def_PunctSketch_IsBoundarySampler

namespace PunctSketch

/-- **Lemma 5.2 (the Borůvka process).** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), Lemma 5.2, p.17. With the sampler's probabilities bounded
as in Lemma 5.1, the probability that the Borůvka process fails to complete or produces a hallucinated
edge over all `R` rounds is at most `n^{−(k+3)}`.

For any finite coin space `Ω` and any `BS` that is a boundary sampling oracle for `G ∖ F` with failure
`e^{−2k}` and hallucination `n^{−(k+5+a)}`, with independent uniform coins per round and
`R = 10 (a + 1) ⌈log_{4/3} n⌉` rounds, the process fails with probability at most `n^{−(k+3+a)}`.

**Formalization Note.** `a = 0` is the printed statement. The threshold `n₀` is the paper's standing "n
is large enough": the union bound over the sampler calls needs `R` small against `n`. `n₀` depends on
`a` only. -/
theorem lemma_5_2 (a : ℕ) :
    ∃ n₀ : ℕ, ∀ (n k : ℕ) {Ω : Type} [Fintype Ω] [Nonempty Ω], n₀ ≤ n → 2 ≤ n → 1 ≤ k → k < n →
      ∀ (BS : Finset (Fin n) → Ω → Option (Sym2 (Fin n))) (G : SimpleGraph (Fin n))
        (F : Finset (Fin n)), F.card < k →
        IsBoundarySampler G F (Real.exp (-(2 * (k : ℝ)))) (((n : ℝ) ^ (k + 5 + a))⁻¹) BS →
        coinProb (fun ω : Fin (boruvkaRounds a n) → Ω => BoruvkaFails G BS F ω) ≤
          ((n : ℝ) ^ (k + 3 + a))⁻¹ := by sorry

end PunctSketch
