-- Prove2me | Theorems.Thm_SemiStreamMWM_Supplement_theorem_1_2
-- name    : SemiStreamMWM.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:36:00.980342+00:00
-- url     : https://prove2.me/theorems/d19d2e52-e96a-4c13-9347-2debbf19be48
-- title:
--   Theorem 1.2 — deterministic incremental $(1-\varepsilon)$-MWM in total time $O((m\varepsilon^{-3}+n\varepsilon^{-6})\log^3 n)$
-- statement:
--   Let $n\ge 0$, let $W\ge1$ be an integer weight bound with $W\le (n+2)^{\kappa}$ for a fixed exponent $\kappa$, and let $0<\varepsilon\le 1/4$. Consider any valid sequence of $m$ edge insertions into the empty graph on $n$ vertices, with integer weights in $[1,W]$, and let $G_i$ be the graph after the first $i$ insertions.
--
--   **Theorem 1.2.** For every $\kappa$ there are a deterministic word-RAM program $P$ (no random instructions), a word-size factor $c_w$ and a constant $A$ such that, for all $n$, $W$, $\varepsilon$ and insertion sequences as above, when $P$ runs in the incremental protocol with words of $c_w\,\ell(n+K+W)$ bits, $K=\lceil 1/\varepsilon\rceil$:
--
--   1. at the completed state after the initialization and after each insertion $i\le m$, the output so far decodes to a matching $M_i$ of $G_i$ with
--   $$w(M_i)\ \ge\ (1-\varepsilon)\,\mu_w(G_i);$$
--   2. the total number of executed instructions over the initialization and all $m$ insertions is finite and at most
--   $$A\left(\frac{m}{\varepsilon^{3}}+\frac{n+1}{\varepsilon^{6}}\right)\log_2^3(n+2).$$
--
--   This is the first incremental algorithm for approximate maximum weight matching in general graphs with update time polynomial in $1/\varepsilon$ and $\log n$; previously such bounds were known only for bipartite graphs, and general graphs had $\varepsilon^{-O(1/\varepsilon)}$ amortized update time even for unweighted matching.
--
--   **Formalization Note** The model is the published `DynBrooks` word RAM with the incremental protocol `SemiStreamMWM.Supplement.Incremental`. $P$, $c_w$ and $A$ are fixed after $\kappa$ and before $n$, $W$, $\varepsilon$, the weights and the sequence; the machine receives only $K=\lceil1/\varepsilon\rceil$, not $\varepsilon$. A deterministic program against a fixed sequence covers adaptive adversaries. "Explicit" is read as: the append-only output, decoded by toggling pairs, is the matching; each write is a charged step.
--
--   Differences from the source:
--   - generalization: weights in $[1,W]$ with $W\ge 8$ a power of two and $W=n^{O(1)}$ (footnote 1) → any integer $W\ge1$ with $W\le(n+2)^\kappa$; reason: drops the power-of-two and $W\ge8$ conditions; every instance of the source satisfies the Lean hypotheses, so the Lean statement specializes to the source.
--   - encoding: $O((m\varepsilon^{-3}+n\varepsilon^{-6})\log^3 n)$ → $A\,(m\varepsilon^{-3}+(n+1)\varepsilon^{-6})\log_2^3(n+2)$ with $A$ fixed after $\kappa$ and the program; reason: the meaning of $O$ for one fixed algorithm; $n+1$ and $\log_2(n+2)$ keep the bound nonzero at $n\le1$ and agree with $n$ and $\log n$ up to constant factors for $n\ge2$.
--   - encoding: "word RAM with $\Theta(\log n)$-bit words" → `DynBrooks` program with word size $c_w\,\ell(n+K+W)$, $c_w$ fixed with the program; reason: the base mission's model (Theorem 1.1); $\ell(n+K+W)=\Theta(\log n)$ whenever $\varepsilon\ge n^{-O(1)}$, which the paper assumes without loss of generality (p.8).
--   - encoding: "explicit $(1-\varepsilon)$-MWM … maintained … through $m$ edge insertions" → the toggle decoding of the append-only output is a $(1-\varepsilon)$-MWM of $G_i$ at the completed state after the initialization and after each insertion; reason: the machine's output tape is append-only; every write is a counted step, as in the paper's time analysis.
--   - encoding: $\varepsilon$ → the machine receives $K=\lceil1/\varepsilon\rceil$ and must reach $1-\varepsilon$ for the real $\varepsilon$; reason: a word RAM receives integers; as in the published Theorem 1.1.
-- source:
--   J. Chen, Faster Semi-Streaming and Dynamic Approximate Maximum Weight Matchings in General Graphs: A Unified Framework (STOC 2027 submission, preprint, arXiv:2611.02105, sha256 83213124981525da907e0f2f9e1e9da47f70f80b9aa72c30767fb094e3bf6934), Theorem 1.2, p.4 (restated and proved p.22); model p.3 (footnote 1), p.8

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_SemiStreamMWM_Graph
import Definitions.Def_SemiStreamMWM_StreamModel
import Definitions.Def_SemiStreamMWM_Supplement_Incremental

set_option autoImplicit false

open Classical

namespace SemiStreamMWM.Supplement

/-- J. Chen, *Faster Semi-Streaming and Dynamic Approximate Maximum Weight Matchings in General
Graphs: A Unified Framework* (STOC 2027 submission, arXiv:2611.02105, sha256 83213124…),
Theorem 1.2, p.4 (restated and proved p.22), with the model of p.3 (footnote 1) and p.8.

"For 0 < ε ≤ 1/4, starting from the empty n-vertex graph, an explicit (1 − ε)-MWM can be maintained
deterministically through m edge insertions in total time O((mε^−3 + nε^−6) log^3 n)."

**Formalization Note.**
* The machine is the published `DynBrooks` word RAM; deterministic means no `coin` instruction
  (`IsDeterministic`). The word size is `cw · ℓ(n + K + W)`, `Θ(log n)` bits since `K` and `W` are
  polynomial in `n` in the relevant range; it does not depend on `m`.
* The paper's `W = n^{O(1)}` (footnote 1) is `W ≤ (n + 2)^κ`; the exponent `κ` is fixed first, then
  the program `P`, the word-size factor `cw` and the constant `A` of the `O`; after them come `n`,
  `W`, `ε`, the weights and the insertion sequence. Any `W ≥ 1` is allowed (footnote 1 asks for
  `W ≥ 8` a power of two).
* Protocol (`incConfig`): the header `n, W, K` with `K = ⌈1/ε⌉` is read first; each insertion
  `{u, v}` delivers `u + 1, v + 1, w_{uv}`. Since `P` is deterministic, a fixed sequence is the same
  as an adaptive adversary. `G_i` is the graph of the first `i` insertions (`G_0` is empty).
* "Explicit (1 − ε)-MWM after each update": at the completed state after the initialization and
  after every insertion `i ≤ m`, the output so far, decoded by toggling pairs (`toggleDecode`), is a
  matching of `G_i` of weight `≥ (1 − ε) µ_w(G_i)`.
* "Total time": the sum of the step counts of the initialization and of all `m` insertions is a
  finite `T` with `T ≤ A (m ε^{-3} + (n + 1) ε^{-6}) log₂(n + 2)³`. `n + 1` and `log₂(n + 2)` replace
  `n` and `log n` so that the bound is not `0` at `n ≤ 1`; they agree up to constant factors for
  `n ≥ 2`. -/
theorem theorem_1_2 :
    ∀ κ : ℕ, ∃ (P : DynBrooks.Program) (cw : ℕ) (A : ℝ), IsDeterministic P ∧
      ∀ (n W : ℕ) (ε : ℝ) (wt : Sym2 (Fin n) → ℕ) (es : List (Fin n × Fin n)),
        0 < ε → ε ≤ 1 / 4 → 1 ≤ W → W ≤ (n + 2) ^ κ → IsInsertionSeq W wt es →
        let K := ⌈1 / ε⌉₊
        let w := cw * ell (n + K + W)
        let hdr := [n, W, K]
        let ops := fun j => (es.map (insWords wt)).getD j []
        (∀ i ≤ es.length, ∃ c, incConfig P w hdr ops i = some c ∧
          ∃ D, toggleDecode n c.output = some D ∧ IsApproxMWMSet (insGraph (es.take i)) wt ε D) ∧
        ∃ T : ℕ, totalTime P w hdr ops es.length = (T : ℕ∞) ∧
          (T : ℝ) ≤ A * ((es.length : ℝ) / ε ^ 3 + ((n : ℝ) + 1) / ε ^ 6) *
            Real.logb 2 ((n : ℝ) + 2) ^ 3 := by sorry

end SemiStreamMWM.Supplement
