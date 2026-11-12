-- Prove2me | Theorems.Thm_QuantumScalingMWPM_QLiquidationist_theorem_4
-- name    : QuantumScalingMWPM.QLiquidationist.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:13:19.053232+00:00
-- url     : https://prove2.me/theorems/6b8248f7-7280-41df-a99b-db4000c9696b
-- title:
--   Theorem 4 — maximum-weight perfect matching in $\tilde O(nm^{2/3}\log W)$ QRAM time with probability $1-n^{-c}$
-- statement:
--   Let $G=(V,E)$ be a simple graph that admits a perfect matching, with $n=|V|$ and $m=|E|$, in the dense regime
--   $$n^{3/2}\le m\le n^{2}.$$
--   Let the edge weights be integers with $|w(e)|\le W$.
--
--   For every constant $c>0$ there are a program in the QRAM model of §1.1, a word-width constant and constants $C>0$ and $\kappa\in\mathbb N$, all fixed before the input, such that the following holds on every encoding of every such $(G,w)$. With probability at least $1-n^{-c}$ over the measurement outcomes, the program
--   1. halts within time
--   $$C\bigl(1+n\,m^{2/3}\max(1,\log_2W)\bigr)\bigl(\log_2(n+2)\bigr)^{\kappa},$$
--   that is, $\tilde O(nm^{2/3}\log W)$;
--   2. keeps every register within $O(\log(n+m+W))$ bits;
--   3. outputs the mate list of a maximum-weight perfect matching of $G$.
--
--   The running time counts every classical step, every update of the memory read by quantum calls, and every gate, query and qubit. In the dense regime it improves on the best known classical combinatorial bound $\tilde O(m\sqrt n\log W)$.
--
--   **Formalization Note** At $n=0$, $0^{-c}=0$, so the empty instance must be solved with probability $1$, which is achievable. The bound $m\le n^2$ holds for every simple graph and is not a hypothesis.
--
--   Differences from the source:
--   - reading: QLIQUIDATIONIST can be implemented so that, with probability at least 1 − n^{−c}, it returns a maximum-weight perfect matching in time Õ(nm^{2/3} log W) → there exist a program P, a width constant and C > 0, κ (chosen after c, before the input) such that, for every input, the probability of the joint event (halting within the time bound, registers within the word length, output decoding to a maximum-weight perfect matching) is ≥ 1 − n^{−c}; reason: "can be implemented" asserts the existence of an implementation in the model of §1.1; the procedures of QLIQUIDATIONIST taken from [13] are not defined in the source, so the existential is over programs; the algorithm, its correctness and its running time are not hypotheses
--   - reading: log W → max(1, log₂ W); reason: for W ∈ {0, 1} the printed factor is ≤ 0 and the bound would be vacuous; for W ≥ 2 the two agree
--   - encoding: Õ(nm^{2/3} log W) → C(1 + n m^{2/3} max(1, log₂ W))(log₂(n+2))^κ with C, κ uniform; reason: Õ hides polylogarithmic factors in n and m (footnote 1, p. 2), and log m ≤ 2 log n; the additive 1 only matters at n = 0, where n m^{2/3} = 0
--   - encoding: dense regime n^{3/2} ≤ m ≤ n² → hypothesis n^{3/2} ≤ m only; reason: m ≤ n(n−1)/2 ≤ n² holds for every simple graph, so no instance is excluded
--   - encoding: the graph, its weights, the returned matching, and the running time in the QRAM model → the input list [n, m, u₁, v₁, w(u₁v₁), …] in any edge order; the output mate list decoded by mateOfList; time = accumulated cost in the Machine definition; probability = succProb over measurement outcomes; reason: fixed encodings shared by every instance; loading the input and building any data structure are charged to the program
-- source:
--   Kourosh Mirsohi, Sandy Irani, Michael Goodrich, STOC 2027 submission #842 (October 2026), Theorem 4, p. 28 (proof p. 28; dense regime p. 4 and pp. 26–28); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/842.pdf

import Mathlib
import Definitions.Def_QuantumScalingMWPM_QLiquidationist_Machine
import Definitions.Def_QuantumScalingMWPM_QLiquidationist_Graph

namespace QuantumScalingMWPM.QLiquidationist

/-- Theorem 4 (p. 28). For every constant `c > 0` there are one QRAM-model program, fixed before
the input, and constants `C > 0`, `k`, such that on every simple graph `G` on `n` vertices with
`m ≥ n^{3/2}` edges that admits a perfect matching, every integer weight function with
`|w(e)| ≤ W`, and every input encoding of `(G, w)`, with probability at least `1 − n^{−c}` the
program halts within time `C · (1 + n m^{2/3} max(1, log₂ W)) · (log₂(n + 2))^k`, keeps every
register within the word length, and outputs the mate list of a maximum-weight perfect
matching. -/
theorem theorem_4 (c : ℝ) (hc : 0 < c) :
    ∃ (P : Program) (width : ℕ) (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ) (W : ℕ) (I : List ℤ),
        (∃ M, IsPerfectMatchingSet G M) →
        (n : ℝ) ^ ((3 : ℝ) / 2) ≤ (G.edgeSet.ncard : ℝ) →
        (∀ e ∈ G.edgeSet, |w e| ≤ (W : ℤ)) →
        IsInputEncoding G w I →
        let B : ℝ := C * (1 + (n : ℝ) * (G.edgeSet.ncard : ℝ) ^ ((2 : ℝ) / 3) *
            max 1 (Real.logb 2 W)) * (Real.logb 2 ((n : ℝ) + 2)) ^ k
        1 - (n : ℝ) ^ (-c) ≤
          succProb P (wordBits width I) ⌊B⌋₊ (initState I) fun s =>
            (s.cost : ℝ) ≤ B ∧ s.peak < 2 ^ wordBits width I ∧ DecodesMWPM G w (outputOf s) := by sorry

end QuantumScalingMWPM.QLiquidationist
