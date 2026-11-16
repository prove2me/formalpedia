-- Prove2me | Theorems.Thm_PunctSketch_Supplement_theorem_9
-- name    : PunctSketch.Supplement.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:52:57.560429+00:00
-- url     : https://prove2.me/theorems/89ecb336-ec94-4d33-864b-a70e72008d51
-- title:
--   Theorem 9, p.29 — testing $k$-connectivity needs $\Omega(nk)$ total communication and $\Omega(nk)$ insertion-only streaming space
-- statement:
--   There is a constant $C>0$ such that for all integers $k,n$ with $3\le k$ and $2k\le n$ the following two lower bounds hold for deciding whether a simple graph on $\{0,\dots,n-1\}$ is $k$-vertex-connected with error probability at most $1/3$ on every input.
--
--   1. **Distributed sketching with public coins.** Let shared coins $\omega$ be drawn from any discrete distribution $\mu$; node player $v$ sends a bit string $\mathrm{enc}_\omega(v,N(v))$ and the coordinator answers $\mathrm{dec}_\omega$ of the $n$ messages. If for every graph $G$ the answer differs from "$G$ is $k$-connected" with probability at most $1/3$, then
--      - for some graph $G$ and some coin outcome $\omega$ of positive probability, $\sum_{v}\lvert\mathrm{enc}_\omega(v,N_G(v))\rvert\ge C\,nk$, and
--      - for some graph $G$, some coin outcome $\omega$ of positive probability and some vertex $v$, $\lvert\mathrm{enc}_\omega(v,N_G(v))\rvert\ge C\,k$.
--   2. **One-pass insertion-only streaming.** Let a streaming algorithm with coins $\omega\sim\mu$ start from the memory state $\mathrm{init}_\omega$, update it by $\mathrm{upd}_\omega$ on each arriving edge insertion and answer $\mathrm{out}_\omega$ at the end. If on every stream of edge insertions in which every edge is inserted at most once the answer differs from "the final graph is $k$-connected" with probability at most $1/3$, then on some such stream, for some coin outcome of positive probability, some memory state reached has at least $C\,nk$ bits.
--
--   All encoders, coordinators and update rules are arbitrary functions; no linearity is assumed.
--
--   Part 1 shows that the linear dependence on $k$ of the per-vertex cost $O(k\log^3 n)$ of the public-coin protocol of Theorem 6 cannot be avoided, and Part 2 that the $O(kn\log^3 n)$ space of its turnstile algorithm is optimal up to polylogarithmic factors, even for insertion-only streams without repeated edges.
--
--   **Formalization Note** The streaming algorithm may read the coins at every step, the strongest model; space is the longest memory state reached on any prefix of the stream.
--
--   Differences from the source:
--   - reading: Ω(nk) total communication, Ω(k) bits for some vertex, Ω(nk) bits of space → one constant C > 0 such that, for all 3 ≤ k with 2k ≤ n, the three worst cases are at least C·n·k, C·k and C·n·k; reason: the Ω is over the stated domain 3 ≤ k ≤ n/2; the reduction (pp.28–29) has N = s·t² index bits with s = ⌊n/k⌋ − 1 ≥ 1, t = ⌊(k−1)/2⌋ ≥ 1, so N ≥ c₀ n k for an absolute c₀
--   - encoding: public randomness, error at most 1/3 on every input; worst-case communication → coins ω from an arbitrary discrete distribution μ : PMF Ω on any Ω : Type, shared by all players and the coordinator; for every graph the error event has probability ≤ 1/3; worst case over all graphs and all ω of positive probability (ω ∈ μ.support); reason: once message lengths are bounded the protocol takes finitely many deterministic forms, so every randomized protocol induces such a distribution; deterministic and private-coin protocols are special cases
--   - encoding: total communication of a vertex-message protocol → Σ_v |enc ω v (N(v))| on one graph and one coin outcome; reason: the sum of the message lengths is the total number of bits sent
--   - generalization: a one-pass streaming algorithm with memory of S bits → init ω, upd ω, out ω all read the coins at every step; memory a bit string of any length; space = the longest memory state reached on any prefix (including the empty one) of any valid stream for ω in the support; reason: an algorithm that stores its random bits in memory is the special case where upd and out ignore ω; the index reduction (p.29) lets Bob continue with the same public coins, so the bound holds for the stronger model
--   - encoding: insertion-only stream in which every edge is inserted at most once; simple n-vertex graph → lists σ of Update n with insert = true for every element and IsValidStream σ (distinct endpoints, an edge is inserted only when absent), in any order and of any length; the decided graph is streamGraph σ; reason: IsValidStream with only insertions is exactly the insertion-only streams without repeated edges; the base mission’s published stream model
--   - encoding: V = [n], N(v) a set, "k-connected" → Fin n, the bit mask nbrMask G v, Balinski61.Connectivity.IsNTuplyConnected G k; reason: Lean convention; the base mission’s published definitions
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), Theorem 9, p.29 (PDF p.30); proof §7, pp.27–29 (PDF pp.28–30); Result 3, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_Balinski61_Connectivity_TuplyConnected
import Definitions.Def_PunctSketch_nbrMask
import Definitions.Def_PunctSketch_IsValidStream

namespace PunctSketch.Supplement

/-- **Theorem 9 with Result 3 (second clause).** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak,
*Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission
(manuscript sha256 a630f888…), Theorem 9, p.29 (pdf p.30): "Let 3 ≤ k ≤ n/2. Consider deciding whether
a simple n-vertex graph is k-connected, with error probability at most 1/3 on every input. 1. In the
distributed sketching model, where each vertex knows only its neighbourhood, every protocol requires
Ω(nk) total communication, even with public randomness. In particular, on some input some vertex sends
Ω(k) bits. 2. Every one-pass insertion-only streaming algorithm where every edge is inserted at most
once requires Ω(nk) bits of space. Both bounds hold for arbitrary encoders, without any linearity
assumption."

There is a constant `C > 0` such that for all `3 ≤ k` with `2k ≤ n`:

1. for every public-coin protocol (coins `ω ∼ μ`, player `v` sends `enc ω v (N(v))`, the coordinator
answers `dec ω (messages)`) that errs with probability at most `1/3` on every graph on `Fin n`, there
are a graph and coins in the support with total communication `Σ_v |message_v| ≥ C n k`, and a graph,
coins in the support and a vertex whose message has at least `C k` bits;

2. for every one-pass streaming algorithm (memory a bit string; `init ω`, `upd ω`, `out ω`) that errs
with probability at most `1/3` on every insertion-only stream in which every edge is inserted at most
once, some memory state reached on some prefix of some such stream, for coins in the support, has at
least `C n k` bits.

**Formalization Note.** The coins are drawn from an arbitrary discrete distribution `μ : PMF Ω` on an
arbitrary type `Ω` and are shared by all players (public coins; deterministic and private-coin
protocols are special cases). Worst case is over all inputs and all coins of positive probability.
Encoders, coordinator, `init`, `upd`, `out` are arbitrary functions, all reading the coins. Streams are
lists of edge insertions (`insert = true`) that are valid in the sense of the base mission
(`IsValidStream`: distinct endpoints, an edge is inserted only when absent), in any order and of any
length; the decided graph is the final graph `streamGraph σ`. -/
theorem theorem_9 :
    ∃ C : ℝ, 0 < C ∧
      ∀ n k : ℕ, 3 ≤ k → 2 * k ≤ n →
        (∀ (Ω : Type) (μ : PMF Ω) (enc : Ω → Fin n → List Bool → List Bool)
            (dec : Ω → (Fin n → List Bool) → Bool),
          (∀ G : SimpleGraph (Fin n),
            μ.toOuterMeasure {ω | ¬ (dec ω (fun v => enc ω v (nbrMask G v)) = true ↔
              Balinski61.Connectivity.IsNTuplyConnected G k)} ≤ 1 / 3) →
          (∃ (G : SimpleGraph (Fin n)) (ω : Ω), ω ∈ μ.support ∧
              C * n * k ≤ ((∑ v : Fin n, (enc ω v (nbrMask G v)).length : ℕ) : ℝ)) ∧
          (∃ (G : SimpleGraph (Fin n)) (ω : Ω) (v : Fin n), ω ∈ μ.support ∧
              C * k ≤ ((enc ω v (nbrMask G v)).length : ℝ))) ∧
        (∀ (Ω : Type) (μ : PMF Ω) (init : Ω → List Bool)
            (upd : Ω → List Bool → Update n → List Bool) (out : Ω → List Bool → Bool),
          (∀ σ : List (Update n), IsValidStream σ → (∀ e ∈ σ, e.insert = true) →
            μ.toOuterMeasure {ω | ¬ (out ω (σ.foldl (upd ω) (init ω)) = true ↔
              Balinski61.Connectivity.IsNTuplyConnected (streamGraph σ) k)} ≤ 1 / 3) →
          ∃ (σ : List (Update n)) (ω : Ω) (j : ℕ), IsValidStream σ ∧ (∀ e ∈ σ, e.insert = true) ∧
            ω ∈ μ.support ∧ j ≤ σ.length ∧
            C * n * k ≤ (((σ.take j).foldl (upd ω) (init ω)).length : ℝ)) := by sorry

end PunctSketch.Supplement
