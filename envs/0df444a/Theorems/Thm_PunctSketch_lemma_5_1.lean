-- Prove2me | Theorems.Thm_PunctSketch_lemma_5_1
-- name    : PunctSketch.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:47:44.066614+00:00
-- url     : https://prove2.me/theorems/2d96562f-a86c-4927-9045-5e2ebd56b9ac
-- title:
--   Lemma 5.1, p.16 — the boundary sampler: failure $e^{-2k}$, hallucination $n^{-(k+5)}$
-- statement:
--   Let $a\ge0$, $n\ge2$, $1\le k<n$, and let $Q>n^3$ be prime. Take any sketching matrix and decoder that form a puncturable retrieval scheme with capacity $33k$, and any rule that picks an element of a nonempty set. For every graph $G$ and every $F$ with $|F|<k$, the sampler that scans the subsampling levels from the top, with fingerprints of collision parameter $c=k+5+a$, is, over one round's coins, a boundary sampling oracle for $G\setminus F$ with
--   $$\text{failure probability}\le e^{-2k},\qquad\text{hallucination probability}\le n^{-(k+5+a)}.$$
--   The case $a=0$ is the printed lemma. A larger $a$ is what gives the goal its error $n^{-c}$ for every $c$.
--
--   Differences from the source:
--   - generalization: n^{−(k+5)}, fingerprint with n^{−(k+5)} collision probability → parameter a, with c = k + 5 + a and hallucination n^{−(k+5+a)}; reason: a = 0 is the printed statement
--   - generalization: n large (standing assumption, p.4) → every n ≥ 2; reason: the proof’s arithmetic needs no threshold: (Q − 1)^{c+1} ≥ n^{3(k+6+a)} beats the number of levels
--   - generalization: the Vandermonde sketch of Theorem 4 at capacity 33k → any matrix and decoder with the capacity-33k guarantee, and any rule picking the returned edge; reason: the proof uses only that guarantee; Theorem 4 at d = 33k is one instance
--   - reading: a suitably large prime Q = Θ(n³) → any prime Q > n³, with n ≥ 2; reason: fixes the unspecified constant of Θ; the primes in (n³, 2n³], which exist by Bertrand, are of that size
--   - reading: "Let b be the vector retrieved at this level", whose fingerprint reads only pairs with v ∈ C, u ∉ C ∪ F → the retrieved set is first cut down to its pairs crossing C; reason: otherwise a junk non-crossing pair would pass the check unread and could be returned
--   - encoding: 0 ≤ l ≤ 2 log n, with l ∈ {0, …, ⌈2 log n⌉} on p.15 → Fin (Nat.clog 2 (n²) + 1); reason: Nat.clog 2 (n²) = ⌈2 log₂ n⌉
--   - encoding: E_{r,l} contains each edge with probability 2^{−l}; 𝒓 uniform on 𝔽_Q ∖ {0} → coins uniform on Fin (2^l) and on (ZMod Q)ˣ, per pair and per level; reason: same distribution; the coordinates on the diagonal of Sym2 are not read
--   - encoding: vertices [n] = {1, …, n} → Fin n, zero-indexed; reason: Lean convention; same instances
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), Lemma 5.1, p.16 (PDF p.17); proof, pp.16–17 (PDF pp.17–18)

import Mathlib
import Definitions.Def_PunctSketch_samplerOutput
import Definitions.Def_PunctSketch_IsBoundarySampler

namespace PunctSketch

/-- **Lemma 5.1 (the boundary sampler).** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), Lemma 5.1, p.16. For `|F| < k` and each query `C`, the
sampler built from the sparse-recovery sketches and the fingerprints fails with probability at most
`e^{−2k}` and hallucinates with probability at most `n^{−(k+5)}`.

For every decoder with the capacity-`33k` guarantee of Theorem 4 (its junk returns are what the
fingerprint defends against) and any rule `pick` choosing an element of a nonempty set, the sampler
with fingerprint parameter `c = k + 5 + a`, over one round's coins, is a boundary sampling oracle for
`G ∖ F` with failure `e^{−2k}` and hallucination `n^{−(k+5+a)}`.

**Formalization Note.** `a = 0` is the printed statement; a larger `a` gives the goal its error `n^{−c}`
for every `c`. Stated for every `n ≥ 2`; the paper tacitly takes `n` large. The decoder sees the
subsampling coins of the level through the sketches and never sees `𝒓`, which is the independence the
proof uses. -/
theorem lemma_5_1 (a : ℕ) {n k Q D : ℕ} [Fact Q.Prime] (hn : 2 ≤ n) (hk : 1 ≤ k) (hkn : k < n)
    (hQ : n ^ 3 < Q) (Ψ : Matrix (Fin D) (Fin n) (ZMod Q))
    (dec : Finset (Fin n) → Finset (Fin n) → (Fin n → Fin D → ZMod Q) → Finset (Sym2 (Fin n)))
    (hdec : IsPuncturableRetrieval k (33 * k) Ψ dec)
    (pick : Finset (Sym2 (Fin n)) → Sym2 (Fin n)) (hpick : ∀ b, b.Nonempty → pick b ∈ b)
    (G : SimpleGraph (Fin n)) (F : Finset (Fin n)) (hF : F.card < k) :
    IsBoundarySampler G F (Real.exp (-(2 * (k : ℝ)))) (((n : ℝ) ^ (k + 5 + a))⁻¹)
      (fun C (ω : RoundCoins n Q (levelTop n)) =>
        samplerOutput Ψ dec pick (k + 5 + a) k G F C ω) := by sorry

end PunctSketch
