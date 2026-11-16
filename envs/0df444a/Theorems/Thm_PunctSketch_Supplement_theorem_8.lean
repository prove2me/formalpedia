-- Prove2me | Theorems.Thm_PunctSketch_Supplement_theorem_8
-- name    : PunctSketch.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:52:24.82248+00:00
-- url     : https://prove2.me/theorems/6f620288-15ab-46ba-9fa3-a8b0397d3c6e
-- title:
--   Theorem 8, p.22 — deterministic protocols for $k$-connected vs disconnected need messages of $\Omega(n/(\sqrt n+k))$ bits
-- statement:
--   There is a constant $C>0$ with the following property. Let $n\ge 2$ and $1\le k\le n-1$, and consider any **deterministic** simultaneous-message protocol on graphs with vertex set $\{0,\dots,n-1\}$: node player $v$ sends a bit string $f_v(N(v))$ that depends only on its identifier and its neighbourhood, and the coordinator computes a Boolean answer from the $n$ messages. Suppose the protocol solves the promise problem of distinguishing $k$-connected graphs from disconnected graphs, i.e. it answers *yes* on every $k$-vertex-connected graph and *no* on every disconnected graph (graphs that are neither are unconstrained). Then its worst-case maximum message length satisfies
--   $$B=\max_{G,\,v}\,\lvert f_v(N_G(v))\rvert\ \ge\ C\,\frac{n}{\sqrt n+k},$$
--   equivalently $B=\Omega(\min\{\sqrt n,n/k\})$. The encoders and the coordinator are arbitrary functions; no linearity is assumed.
--
--   For $k=1$ this is an $\Omega(\sqrt n)$ deterministic lower bound for connectivity, nearly matching the private-coin upper bound of Holm et al. and improving the $\Omega(n^{1/3})$ bound of Robinson and Tan.
--
--   **Formalization Note** The maximum ranges over all graphs on $n$ vertices, including graphs outside the promise; messages may have any length.
--
--   Differences from the source:
--   - reading: B = Ω(n/(√n + k)) "for every n ≥ 2 and 1 ≤ k ≤ n − 1" → one constant C > 0 with B ≥ C·n/(√n + k) for all n ≥ 2 and 1 ≤ k ≤ n − 1; reason: the Ω is over the theorem’s stated domain; the proof (p.24) gives an explicit constant from q = 128(⌈√n⌉ + k), M < 4(qB + k) and B ≥ 1
--   - encoding: B = Ω(min{√n, n/k}) → only the form n/(√n + k) is stated; reason: min{√n, n/k}/2 ≤ n/(√n + k) ≤ min{√n, n/k}, so the two forms differ by a factor at most 2
--   - encoding: messages from an alphabet of size at most 2^B; worst-case maximum message length → messages are bit strings of arbitrary length; the conclusion is that some player on some graph on Fin n (in or outside the promise) sends at least C·n/(√n + k) bits; reason: the worst-case maximum is the maximum over all players and all neighbourhoods, which the proof’s pigeonhole (Lemmas 6.2, 6.3) counts; strings of length ≤ B number fewer than 2^{B+1}, a constant change
--   - encoding: deterministic encoders f_v(N(v)) and a coordinator, for the promise problem k-connected vs disconnected → f : Fin n → List Bool → List Bool applied to nbrMask G v, dec a function of the messages indexed by sender, both chosen after n and k; correctness required only on k-connected (IsNTuplyConnected G k) and on disconnected (¬ G.Connected) graphs; reason: Lean convention; arbitrary functions as "arbitrary encoders, without any linearity assumption"
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), Theorem 8, p.22 (PDF p.23); proof §6.1–6.2, pp.23–26 (PDF pp.24–27); Result 3, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_Balinski61_Connectivity_TuplyConnected
import Definitions.Def_PunctSketch_nbrMask

namespace PunctSketch.Supplement

/-- **Theorem 8 with Result 3 (first clause).** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak,
*Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission
(manuscript sha256 a630f888…), Theorem 8, p.22 (pdf p.23): "For every n ≥ 2 and 1 ≤ k ≤ n − 1, every
deterministic simultaneous-message protocol for this promise problem has worst-case maximum message
length B = Ω(n/(√n + k)) = Ω(min{√n, n/k}). The bound holds for arbitrary encoders, without any
linearity assumption."

There is a constant `C > 0` such that for all `n ≥ 2`, `1 ≤ k ≤ n − 1`, every encoder `f` (player `v`
sends `f v (N(v))`) and every coordinator `dec` (a function of the `n` messages) that answers `true` on
every `k`-connected graph and `false` on every disconnected graph, some player on some graph sends at
least `C · n / (√n + k)` bits.

**Formalization Note.** Deterministic: no coins. The encoder and coordinator are arbitrary functions
(no linearity, no computability), chosen after `n` and `k`, so they may depend on them. Messages are bit
strings of arbitrary length; the worst-case maximum message length `B` is the maximum of the message
lengths over all players and all graphs on `Fin n` (including graphs outside the promise), so
`B ≥ C n/(√n + k)` is "some player on some graph sends at least that many bits". Graphs that are
neither `k`-connected nor disconnected are unconstrained. -/
theorem theorem_8 :
    ∃ C : ℝ, 0 < C ∧
      ∀ n k : ℕ, 2 ≤ n → 1 ≤ k → k ≤ n - 1 →
        ∀ (f : Fin n → List Bool → List Bool) (dec : (Fin n → List Bool) → Bool),
          (∀ G : SimpleGraph (Fin n), Balinski61.Connectivity.IsNTuplyConnected G k →
            dec (fun v => f v (nbrMask G v)) = true) →
          (∀ G : SimpleGraph (Fin n), ¬ G.Connected →
            dec (fun v => f v (nbrMask G v)) = false) →
          ∃ (G : SimpleGraph (Fin n)) (v : Fin n),
            C * n / (Real.sqrt n + k) ≤ ((f v (nbrMask G v)).length : ℝ) := by sorry

end PunctSketch.Supplement
