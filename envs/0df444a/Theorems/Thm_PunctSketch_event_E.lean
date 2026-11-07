-- Prove2me | Theorems.Thm_PunctSketch_event_E
-- name    : PunctSketch.event_E
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:47:32.839014+00:00
-- url     : https://prove2.me/theorems/6a71ac5f-ea90-4670-b13a-6fd075c46f36
-- title:
--   §5.4, p.21 — the event $\mathcal E$: spanning forests for all $|F|<k$ simultaneously
-- statement:
--   Let $a\ge0$. There is $n_0$ such that for $n\ge n_0$, $1\le k<n$, every prime $Q>n^3$, every matrix and decoder with the capacity-$33k$ guarantee, every picking rule and every graph $G$, with probability at least $1-n^{-(3+a)}$ over one coin string for the whole protocol,
--   $$\text{for all }F\text{ with }|F|<k:\quad\mathcal T(F)\text{ is a spanning forest of }G\setminus F,$$
--   where $\mathcal T(F)$ is the output of the Borůvka process on the sketches, using the sampler of Lemma 5.1 with fingerprint parameter $k+5+a$.
--
--   Simultaneity is the point: the coordinator of §5.4 chooses each $F$ from earlier answers, which is allowed because this event covers all $F$ at once.
--
--   Differences from the source:
--   - generalization: "with high probability" → 1 − n^{−(3+a)} for each a; reason: the union bound of Lemmas 5.1 and 5.2 over at most n^k sets gives it; a = 0 gives 1 − n^{−3}
--   - reading: n large (standing assumption, p.4) → ∃ n₀ depending on a only; reason: inherited from Lemma 5.2
--   - generalization: the Vandermonde sketch of Theorem 4 → any matrix and decoder with the capacity-33k guarantee, and any picking rule; reason: the proof uses only that guarantee
--   - reading: a suitably large prime Q = Θ(n³) → any prime Q > n³, with n ≥ 2; reason: fixes the unspecified constant of Θ; the primes in (n³, 2n³], which exist by Bertrand, are of that size
--   - encoding: vertices [n] = {1, …, n} → Fin n, zero-indexed; reason: Lean convention; same instances
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §5.1, pp.16–17 (PDF pp.17–18); §5.4, p.21 (PDF p.22)

import Mathlib
import Definitions.Def_PunctSketch_BoruvkaFails
import Definitions.Def_PunctSketch_samplerOutput
import Definitions.Def_PunctSketch_coinProb

namespace PunctSketch

/-- **The event ℰ.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §5.4, p.21: "the preceding analysis gives an event ℰ, holding with high
probability, on which 𝒯(F) is a spanning forest of G ⧵ F for every |F| < k simultaneously."

Over one coin string for the whole protocol, with probability at least `1 − n^{−(3+a)}`, the output of
the Borůvka process on the sketches is a spanning forest of `G ∖ F` for all `|F| < k` simultaneously.

**Formalization Note.** A union bound over at most `n^k` sets `F`, from Lemmas 5.1 and 5.2. `a = 0` gives
`1 − n^{−3}`. `n₀` depends on `a` only. -/
theorem event_E (a : ℕ) :
    ∃ n₀ : ℕ, ∀ (n k Q D : ℕ) [Fact Q.Prime], n₀ ≤ n → 2 ≤ n → 1 ≤ k → k < n → n ^ 3 < Q →
      ∀ (Ψ : Matrix (Fin D) (Fin n) (ZMod Q))
        (dec : Finset (Fin n) → Finset (Fin n) → (Fin n → Fin D → ZMod Q) → Finset (Sym2 (Fin n))),
        IsPuncturableRetrieval k (33 * k) Ψ dec →
        ∀ (pick : Finset (Sym2 (Fin n)) → Sym2 (Fin n)), (∀ b, b.Nonempty → pick b ∈ b) →
        ∀ G : SimpleGraph (Fin n),
          1 - ((n : ℝ) ^ (3 + a))⁻¹ ≤
            coinProb (fun ω : Fin (boruvkaRounds a n) → RoundCoins n Q (levelTop n) =>
              ∀ F : Finset (Fin n), F.card < k →
                IsSpanningForestOf G F
                  (boruvkaState (fun C ω₀ => samplerOutput Ψ dec pick (k + 5 + a) k G F C ω₀) F ω
                    (boruvkaRounds a n))) := by sorry

end PunctSketch
