-- Prove2me | Theorems.Thm_PunctSketch_Supplement_theorem_7
-- name    : PunctSketch.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:51:52.568596+00:00
-- url     : https://prove2.me/theorems/5c90286f-898e-4e2d-b8a8-8a9709e84960
-- title:
--   Theorem 7, p.15, with Result 2, p.2 — private-coin $k$-connectivity with $O(\sqrt{kn}\,\log^{3/2} n)$ bits per vertex
-- statement:
--   Let $c>0$. There are a constant $A>0$, coin-alphabet sizes $N(n,k)$, $M(n,k)\ge 1$, message lengths $L(n,k)$, an encoder and a coordinator such that for all integers $1\le k<n$ the following holds.
--
--   Each node player $v$ of a graph $G$ on the vertex set $\{0,\dots,n-1\}$ draws its own **private** coin vector $\omega_v$ uniformly from $\{0,\dots,M-1\}^N$, independently of the other players, and sends a message computed from $n$, $k$, its identifier $v$, its neighbourhood $N(v)$ and $\omega_v$ only. The coordinator sees only $n$, $k$ and the $n$ messages (indexed by sender), uses no coins, runs in time polynomial in its input (one Turing machine for all $n,k$, with $n$ written in unary, so time $\mathrm{poly}(n,k)$), and outputs a certified answer: a flag, a spanning subgraph $H\subseteq G$ and a vertex set $Z$.
--
--   1. Every message has exactly $L(n,k)$ bits, where
--   $$L(n,k)\le A\,\sqrt{kn}\,\log_2^{3/2} n .$$
--   2. For every graph $G$ on $n$ vertices, with probability at least $1-n^{-c}$ over the coins the output is a correct certificate: $H$ has at most $kn-\binom{k+1}{2}$ edges and, for every set $F$ of fewer than $k$ vertices, $H\setminus F$ and $G\setminus F$ have the same connected components; if the flag says *yes*, $G$ and $H$ are $k$-vertex-connected; if it says *no*, $|Z|<k$ and $G\setminus Z$ is disconnected.
--
--   This is the private-coin counterpart of the public-coin protocol of Theorem 6: it shows that $k$-connectivity can be decided with $o(n)$ bits per player without shared randomness, with only a $\sqrt k$ overhead over the $O(\sqrt n\log^{3/2}n)$ connectivity protocol of Holm et al.
--
--   **Formalization Note** "With high probability" is read as every polynomial: $A$ and the protocol may depend on $c$ but not on $n$ or $k$. $k$-connectivity is the published definition: at least $k+1$ vertices, and deleting fewer than $k$ vertices leaves a connected graph. The certificate is the base mission's published `IsCertificate`. Only the coordinator is required to run in polynomial time, as Result 2 states; the encoders are arbitrary functions.
--
--   Differences from the source:
--   - reading: "with high probability" → for every real c > 0, error at most n^{−c} on every graph, with A, N, M, L and the protocol chosen after c and before n, k; reason: the reading of the published goal PunctSketch.theorem_6; the §5.2 proof scales: Lemma 5.3 gives n^{−(k+3)} per pair (F, C) with N = 4kn log n, and a larger multiple of kn log n in N gives any polynomial
--   - reading: Result 2 (p.2): "The coordinator needs only poly(n, k) time to compute their answer and certify it." → dec is one machine for all (n, k), TM2ComputableInPolyTime on DecInput.code (n in unary, k, empty coin field, the messages); its output must satisfy the base IsCertificate (flag, H ≤ G with |E(H)| + C(k+1,2) ≤ kn agreeing with G after every deletion of fewer than k vertices, a separator of fewer than k vertices for "no"); no running time for the encoders; reason: Result 2 is Theorem 7 with this clause; §5.4 (pp.20–22) gives the polynomial-time coordinator and the certificate of kn − C(k+1,2) edges for both protocols ("the private-coin protocol processes at most n components"); Result 2 claims time only for the coordinator; n in unary as in the published goal, so input-polynomial time is poly(n, k)
--   - generalization: "n is large enough" (p.4) and k = o(n/log³ n) (footnote 7, p.15, for all of §5) → every 1 ≤ k < n, with no threshold on n; reason: footnote 7: for larger k each vertex sends its whole neighbourhood, n ≤ A²k log³ n bits, which the bound allows for a suitable A; the printed theorem is the special case
--   - generalization: O(√(kn) log^{3/2} n) bits of communication per node (worst case) → every message has exactly L n k bits, for every neighbourhood and every coin outcome, with L n k ≤ A·√(k n)·(log₂ n)^{3/2}; reason: an exact length implies the worst-case bound
--   - encoding: private randomness of each node player; a deterministic coordinator → player v reads only its own coin vector ω v : Fin N → Fin M, the n vectors independent and uniform (uniform probability coinProb on Fin n → Fin N → Fin M, 1 ≤ M); the coordinator reads n, k and the messages indexed by sender, with no coins (DecInput with coins := []); reason: the protocol of §5.2 uses each player’s own randomness to pick min{√N, deg v} uniform random neighbours, which needs a uniform alphabet that need not be a power of two; the coordinator of §5.2 uses no randomness
--   - encoding: V = [n], N(v) a set, "k-vertex connected" → Fin n, the bit mask nbrMask G v, Balinski61.Connectivity.IsNTuplyConnected G k; reason: Lean convention; the base mission’s published definitions, the paper’s definition of k-connectivity (p.1)
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), Theorem 7, p.15 (PDF p.16); proof §5.2 and Lemma 5.3, p.18 (PDF p.19); Result 2, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_Balinski61_Connectivity_TuplyConnected
import Definitions.Def_PunctSketch_EncInput
import Definitions.Def_PunctSketch_DecInput
import Definitions.Def_PunctSketch_coinList
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_PunctSketch_nbrMask
import Definitions.Def_PunctSketch_IsCertificate

namespace PunctSketch.Supplement

/-- **Theorem 7 with Result 2.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph
Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256
a630f888…), Theorem 7, p.15 (pdf p.16): "There exists a distributed sketching protocol with private
randomness and O(√(kn) log^{3/2} n) bits of communication per node, that solves the k-vertex
connectivity problem with high probability." Result 2, p.2 (pdf p.3): "the node players, using only
private random coins, communicate O(√(kn) log^{3/2} n) bits each and the coordinator errs with
probability at most 1/ poly(n). The coordinator needs only poly(n, k) time to compute their answer and
certify it." Proof in §5.2, p.18 (pdf p.19); the polynomial-time certifying coordinator in §5.4,
pp.20–22 (pdf pp.21–23), which applies to the private-coin protocol.

For every `c > 0` there are a constant `A > 0`, coin-alphabet sizes `N, M`, message lengths `L`, an
encoder `enc` and one polynomial-time coordinator machine `dec` such that for all `1 ≤ k < n`: every
message has exactly `L n k ≤ A √(k n) (log₂ n)^{3/2}` bits, and for every graph `G` on `Fin n` the
coordinator's output fails to be a correct certified answer (`IsCertificate`) with probability at most
`n^{−c}`.

**Formalization Note.** Private coins: player `v` draws its own coin vector
`ω v : Fin (N n k) → Fin (M n k)`, the `n` vectors independent and uniform (the coin space
`Fin n → Fin (N n k) → Fin (M n k)` with the uniform probability `coinProb`). Player `v`'s message
reads only `n`, `k`, its own ID, its neighbourhood `nbrMask G v` and its own coins `ω v`; the
coordinator reads only `n` (in unary), `k` and the list of messages indexed by sender (its coin field is
empty), and is one machine for all `(n, k)`, polynomial time in its input. The alphabet size `M ≥ 1` is
arbitrary (no polynomial bound), since the paper's players pick uniform random neighbours. The encoder
is an arbitrary function: Result 2 claims a running time for the coordinator only. A correct certified
answer is the base mission's `IsCertificate`: a flag with a spanning subgraph `H ≤ G` of at most
`kn − C(k+1,2)` edges agreeing with `G` after every deletion of fewer than `k` vertices, and a separating
set of fewer than `k` vertices for a "no". "With high probability" is every polynomial, the constants and
the protocol chosen after `c` and before `n, k`. -/
theorem theorem_7 (c : ℝ) (hc : 0 < c) :
    ∃ (A : ℝ) (N M L : ℕ → ℕ → ℕ) (enc : EncInput → List Bool) (dec : DecInput → List Bool),
      0 < A ∧
      Nonempty (Turing.TM2ComputableInPolyTime DecInput.code encBits dec) ∧
      ∀ n k : ℕ, 1 ≤ k → k < n →
        1 ≤ M n k ∧
        (L n k : ℝ) ≤ A * Real.sqrt ((k : ℝ) * n) * Real.logb 2 n ^ ((3 : ℝ) / 2) ∧
        (∀ (v : Fin n) (S : Fin n → Bool) (ω : Fin (N n k) → Fin (M n k)), S v = false →
          (enc ⟨n, k, v, List.ofFn S, coinList ω⟩).length = L n k) ∧
        ∀ G : SimpleGraph (Fin n),
          coinProb (fun ω : Fin n → Fin (N n k) → Fin (M n k) =>
            ¬ IsCertificate G k
              (dec ⟨n, k, [],
                List.ofFn (fun v : Fin n => enc ⟨n, k, v, nbrMask G v, coinList (ω v)⟩)⟩)) ≤
            (n : ℝ) ^ (-c) := by sorry

end PunctSketch.Supplement
