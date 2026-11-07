-- Prove2me | Theorems.Thm_PunctSketch_theorem_5
-- name    : PunctSketch.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:44:32.856045+00:00
-- url     : https://prove2.me/theorems/425e3c18-e3ac-456d-9b54-8c9534a5ffa0
-- title:
--   Theorem 5, p.13 — a puncturable fingerprint: size and collision bound (the sampler clause is Lemma 5.1)
-- statement:
--   There is a constant $A>0$ such that for all $n\ge2$, all primes $n^3<Q\le2n^3$ and all $c,k$: the sketch of $c+k$ field elements uses at most $A(c+k)\log_2n$ bits. Moreover, let $|F|<k$, let $C$ be disjoint from $F$, and let $E'$ be a set of pairs, fixed before the coins, whose boundary differs from that of $G$:
--   $$E\cap\mathrm{cross}(F,C)\ne E'\cap\mathrm{cross}(F,C).$$
--   Then for $\boldsymbol r$ uniform on $(\mathbb F_Q\setminus\{0\})^{\text{pairs}}$,
--   $$\Pr\Big[\sum_{v\in C}\tilde{\boldsymbol f}_F(v)=\boldsymbol f(E')\Big]\le(Q-1)^{-(c+k-|F|)}\le n^{-c}.$$
--   The sum on the left is what the coordinator computes from the messages and the right side is what it computes from $\boldsymbol r$, so this bounds the chance that a wrong purported boundary passes the check.
--
--   Differences from the source:
--   - generalization: collision probability at most n^{−c} → at most (Q − 1)^{−(c+k−|F|)}, and this at most n^{−c}; reason: the stronger bound is on p.15 of the proof and implies the printed one; Lemma 5.1 needs it (the union over levels)
--   - generalization: c + k < n → no relation between c + k and n; reason: not used by the argument; the theorem specializes to it
--   - reading: a suitably large prime Q = Θ(n³) → every prime Q with n³ < Q ≤ 2n³, with n ≥ 2; reason: fixes the unspecified constants of Θ; such primes exist by Bertrand
--   - reading: "In turn, they can implement a boundary sampling oracle for G ⧵ F with suitable hallulication and failure probabilities" → stated as the companion item PunctSketch.lemma_5_1; reason: the probabilities are only named there, and it needs the sparse recovery and subsampling of §5.1
--   - encoding: 𝒓 ∈ (𝔽_Q ∖ {0})^m, with the convention 𝒓_{v,v} = 0 → r : Sym2 (Fin n) → (ZMod Q)ˣ uniform, diagonal included; reason: the diagonal coordinates are never read (no self-loops, crossing pairs have distinct ends); same distribution on the coordinates that are read
--   - encoding: vertices [n] = {1, …, n} → Fin n, zero-indexed; reason: Lean convention; same instances
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), Theorem 5, p.13 (PDF p.14); proof, pp.14–15 (PDF pp.15–16)

import Mathlib
import Definitions.Def_PunctSketch_alpha
import Definitions.Def_PunctSketch_fingerprint
import Definitions.Def_PunctSketch_puncture
import Definitions.Def_PunctSketch_boundaryFp
import Definitions.Def_PunctSketch_puncturedBoundary
import Definitions.Def_PunctSketch_coinProb

namespace PunctSketch

/-- **Theorem 5 (puncturable fingerprint): size and collision bound.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), Theorem 5, p.13, and its
proof, pp.14–15. A linear sketch of `O((c + k) log n)` bits, and for every `|F| < k` a fingerprint on
boundary sets of `G ∖ F` with collision probability at most `n^{−c}`.

For `n ≥ 2` and a prime `n³ < Q ≤ 2n³`: `c + k` field elements take at most `A (c + k) log₂ n` bits.
For `|F| < k`, `C` disjoint from `F` and a purported edge set `E′` fixed before the coins, with a
different boundary, `𝒓` uniform on `(𝔽_Q ∖ {0})^{pairs}` gives
`Pr[Σ_{v∈C} 𝒇̃_F(v) = fingerprint of E′] ≤ (Q − 1)^{−(c+k−|F|)} ≤ n^{−c}`.

**Formalization Note.** The first bound is on p.15 and it is what Lemma 5.1 needs. The page's `c + k < n`
is dropped: it reflects the use, and the statement specializes to it. The sampler clause of the
theorem is Lemma 5.1. -/
theorem theorem_5 :
    ∃ A : ℝ, 0 < A ∧ ∀ (n Q : ℕ) [Fact Q.Prime], 2 ≤ n → n ^ 3 < Q → Q ≤ 2 * n ^ 3 → ∀ c k : ℕ,
      (((c + k : ℕ) : ℝ) * (Nat.clog 2 Q : ℝ) ≤ A * ((c : ℝ) + k) * Real.logb 2 n) ∧
      ∀ (G : SimpleGraph (Fin n)) (E' : Set (Sym2 (Fin n))) (F C : Finset (Fin n)),
        F.card < k → Disjoint C F →
        G.edgeSet ∩ crossingPairs F C ≠ E' ∩ crossingPairs F C →
        coinProb (fun r : Sym2 (Fin n) → (ZMod Q)ˣ =>
          ∀ t, t + F.card < c + k →
            ∑ v ∈ C, puncture (alpha Q) F
                (fingerprint G (alpha Q) (fun e => ((r e : (ZMod Q)ˣ) : ZMod Q)) v) v t =
              boundaryFp (alpha Q) F C (fun e => ((r e : (ZMod Q)ˣ) : ZMod Q)) E' t) ≤
          (((Q : ℝ) - 1) ^ (c + k - F.card))⁻¹ ∧
        (((Q : ℝ) - 1) ^ (c + k - F.card))⁻¹ ≤ ((n : ℝ) ^ c)⁻¹ := by sorry

end PunctSketch
