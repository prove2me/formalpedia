-- Prove2me | Theorems.Thm_SemiStreamMWM_lemma_4_5
-- name    : SemiStreamMWM.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:23:36.259971+00:00
-- url     : https://prove2.me/theorems/4ca5db8b-70c2-4d21-a6a4-96baff8bea51
-- title:
--   Lemma 4.5 [BCD+25, Thm 6.11] — reducing the weight range to $\Theta(\varepsilon^{-5})$
-- statement:
--   In the multi-pass semi-streaming model of the mission. There are constants $c_0,c_1,c_2>0$ with $c_1\le c_2$ such that the following holds. Suppose a program $P$ computes a $(1-\varepsilon)$-MWM on every $n$-vertex graph $G$ with $m$ edges and integer weights in $[1,W]$, $W\le c_2\varepsilon^{-5}$, for every order of the edge stream, using at most $p(n,m,\mu(G),W,\varepsilon)$ passes and, at every step, at most $s(n,m,\mu(G),W,\varepsilon)$ bits of space (on the instances allowed by a domain predicate $D(n,\varepsilon)$, with $0<\varepsilon\le1/2$). Then there are a weight range $W'(\varepsilon)$ with $c_1\varepsilon^{-5}\le W'(\varepsilon)\le c_2\varepsilon^{-5}$ and a program $P'$, deterministic whenever $P$ is, that computes a $(1-c_0\varepsilon)$-MWM on every such graph with integer weights in $[1,W]$ for any $W\ge1$, using
--
--   $$\max_{H\le G}p\big(n,|E(H)|,\mu(H),W'(\varepsilon),\varepsilon\big)\ \text{passes and}\ \ c_0\,\max\{1,\lceil\log_{1/\varepsilon}W\rceil\}\cdot\max_{H\le G}s\big(n,|E(H)|,\mu(H),W'(\varepsilon),\varepsilon\big)\ \text{bits},$$
--
--   the maxima over the subgraphs $H$ of $G$ (the weight-class graphs).
--
--   This removes the $\log W$ factor of Lemma 4.4 in favour of $\log(1/\varepsilon)$, giving the second clause of Theorem 1.1.
--
--   Differences from the source:
--   - reading: a semi-streaming algorithm … computes … The reduction preserves determinism → programs P, P′ of the mission's machine with word-size factors cw, cw′, run with the coin tape fixed; IsDeterministic P → IsDeterministic P′; reason: the paper's model is the deterministic word RAM (p.8) and the lemma is used only deterministically (paper.md decisions 2, 10)
--   - reading: resource bounds p(n, m, W, ε), s(n, m, W, ε) and the conclusion's p(n, m, Θ(ε^−5), ε), s(n, m, Θ(ε^−5), ε) → bounds that are functions of (n, m, µ, W, ε); the conclusion's bounds are the maximum over subgraphs H ≤ G of p, s at (n, |E(H)|, µ(H), W′(ε), ε); reason: the proof of Theorem 1.1 applies the lemma with µ-dependent space on the weight-class subgraphs (p.21); equal to the printed bound when p, s are monotone in m and µ
--   - generalization: the base algorithm works for every instance → the base is assumed only on instances with D(n, ε), 0 < ε ≤ 1/2 and W ≤ c₂ε^−5, and the conclusion is asserted on the instances with D(n, ε); reason: D = True and the full weight range recover the printed lemma; the domain predicate lets the lemma compose with Lemma 4.4's polynomial weight range
--   - encoding: Θ(ε^−5), O(ε), O(s · ⌈log_{ε^−1} W⌉) → W′(ε) ∈ [c₁ε^−5, c₂ε^−5]; c₀ε; c₀·max{1, ⌈log_{1/ε} W⌉}·s, with c₀, c₁, c₂ before the base algorithm; reason: same instances; max{1, ·} covers W = 1
--   - reading: every ε for which the statement is meaningful → 0 < ε ≤ 1/2, both in the hypothesis on the base program and in the conclusion; reason: the lemma is an asymptotic statement in ε (O(ε), Θ(ε^−5), log base ε^−1 > 1 needs ε < 1), read with the threshold 1/2; for ε ≥ 1/2 the conclusion's (1 − c₀ε)-MWM is the empty matching once c₀ ≥ 2
-- source:
--   J. Chen, Faster Semi-Streaming and Dynamic Approximate Maximum Weight Matchings in General Graphs: A Unified Framework (STOC 2027 submission, preprint, arXiv:2611.02105, sha256 83213124981525da907e0f2f9e1e9da47f70f80b9aa72c30767fb094e3bf6934), Lemma 4.5 ([BCD+25, Theorem 6.11]), p.21; proof of Theorem 1.1, p.21

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_SemiStreamMWM_Graph
import Definitions.Def_SemiStreamMWM_StreamModel

open Classical

namespace SemiStreamMWM

/-- J. Chen (STOC 2027 submission, arXiv:2611.02105, sha256 83213124…), Lemma 4.5
([BCD+25, Theorem 6.11]), p.21, as used in the proof of Theorem 1.1 (p.21).

"Suppose a semi-streaming algorithm computes a (1 − ε)-MWM on an n-vertex, m-edge graph with weights
in [1, W] using p(n, m, W, ε) passes and s(n, m, W, ε) bits of space. Then a (1 − O(ε))-MWM can be
computed using p(n, m, Θ(ε^−5), ε) passes and O(s(n, m, Θ(ε^−5), ε) · ⌈log_{ε^−1} W⌉) bits of space. The
reduction preserves determinism."

**Formalization Note.** The base algorithm is a program `P` with word-size factor `cw`, run as in
`StreamModel` on the header `n, W, K = ⌈1/ε⌉` and the weighted edges. Its resource bounds are
arbitrary real functions `p, s` of `(n, m, µ, W, ε)` with `m = |E(G)|` and `µ = µ(G)`: the extra
argument `µ` records the paper's use, "Each weight-class graph has maximum matching cardinality at most
µ(G)" (p.21). The base is assumed to work only for `W ≤ c₂ε^{−5}` and on the instances satisfying a
domain predicate `D(n, ε)` (`D = True` is the printed lemma). The conclusion's program `P'` works for
every `W ≥ 1`; `Θ(ε^{−5})` is a weight range `W'(ε) ∈ [c₁ε^{−5}, c₂ε^{−5}]`, and `p(n, m, W'(ε), ε)` and
`s(n, m, W'(ε), ε)` are read as the maximum of the base bounds over the subgraphs `H ≤ G` (the
weight-class graphs), which is the printed bound when `p` and `s` are monotone in `m` and `µ`: the run
uses at most `p(n, |E(H)|, µ(H), W'(ε), ε)` passes for some `H ≤ G`, and at each step at most
`c₀ · max{1, ⌈log_{1/ε} W⌉} · s(n, |E(H)|, µ(H), W'(ε), ε)` bits for some `H ≤ G`. `O(ε)` is `c₀ε`.
`ε ≤ 1/2` makes the base `1/ε` of the logarithm larger than `1`, and `max{1, ·}` covers `W = 1`.
"Preserves determinism" is: if `P` has no `coin` instruction, neither has `P'`. The constants
`c₀, c₁, c₂` come before `D`, `P`, `cw`, `p`, `s`. -/
theorem lemma_4_5 : ∃ c₀ c₁ c₂ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ c₁ ≤ c₂ ∧
    ∀ (D : ℕ → ℝ → Prop) (P : DynBrooks.Program) (cw : ℕ) (p s : ℕ → ℕ → ℕ → ℕ → ℝ → ℝ),
    (∀ (n W : ℕ) (ε : ℝ) (G : SimpleGraph (Fin n)) (wt : Sym2 (Fin n) → ℕ)
        (es : List (Fin n × Fin n)),
        D n ε → 0 < ε → ε ≤ 1 / 2 → 1 ≤ W → (W : ℝ) ≤ c₂ * (1 / ε) ^ 5 →
        (∀ e ∈ G.edgeSet, 1 ≤ wt e ∧ wt e ≤ W) → IsEdgeStream G es →
        let K := ⌈1 / ε⌉₊
        let w := cw * ell (n + K + W)
        let inp := mwmWords W K wt es
        (∀ t, (spaceBits w (passRun P w inp t).1 : ℝ) ≤ s n (edgeCount G) (mcm G) W ε) ∧
        ∃ t, IsHalted P (passRun P w inp t).1 ∧
          ((passRun P w inp t).2 : ℝ) ≤ p n (edgeCount G) (mcm G) W ε ∧
          ∃ M, decodePairs n (passRun P w inp t).1.output = some M ∧ IsMatchingList G M ∧
            (1 - ε) * (mwm G wt : ℝ) ≤ listWeight wt M) →
    ∃ (P' : DynBrooks.Program) (cw' : ℕ) (W' : ℝ → ℕ),
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → c₁ * (1 / ε) ^ 5 ≤ (W' ε : ℝ) ∧ (W' ε : ℝ) ≤ c₂ * (1 / ε) ^ 5) ∧
      (IsDeterministic P → IsDeterministic P') ∧
      ∀ (n W : ℕ) (ε : ℝ) (G : SimpleGraph (Fin n)) (wt : Sym2 (Fin n) → ℕ)
        (es : List (Fin n × Fin n)),
        D n ε → 0 < ε → ε ≤ 1 / 2 → 1 ≤ W →
        (∀ e ∈ G.edgeSet, 1 ≤ wt e ∧ wt e ≤ W) → IsEdgeStream G es →
        let K := ⌈1 / ε⌉₊
        let w := cw' * ell (n + K + W)
        let inp := mwmWords W K wt es
        (∀ t, ∃ H : SimpleGraph (Fin n), H ≤ G ∧
          (spaceBits w (passRun P' w inp t).1 : ℝ) ≤
            c₀ * (max 1 ⌈Real.logb (1 / ε) W⌉₊ : ℕ) * s n (edgeCount H) (mcm H) (W' ε) ε) ∧
        ∃ t, IsHalted P' (passRun P' w inp t).1 ∧
          (∃ H : SimpleGraph (Fin n), H ≤ G ∧
            ((passRun P' w inp t).2 : ℝ) ≤ p n (edgeCount H) (mcm H) (W' ε) ε) ∧
          ∃ M, decodePairs n (passRun P' w inp t).1.output = some M ∧ IsMatchingList G M ∧
            (1 - c₀ * ε) * (mwm G wt : ℝ) ≤ listWeight wt M := by sorry

end SemiStreamMWM
