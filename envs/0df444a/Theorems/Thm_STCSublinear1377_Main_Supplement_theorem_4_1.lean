-- Prove2me | Theorems.Thm_STCSublinear1377_Main_Supplement_theorem_4_1
-- name    : STCSublinear1377.Main.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:26:52.26322+00:00
-- url     : https://prove2.me/theorems/1d4d2436-94fb-4735-adc2-808bd06bdd0f
-- title:
--   Theorem 4.1 — No polynomial-time (2 − ε)-approximation unless P = NP
-- statement:
--   Fix a real $\varepsilon$ with $0<\varepsilon<1$. Suppose a deterministic polynomial-time algorithm, on every connected simple unweighted graph $G$ on $n\ge2$ vertices, returns a spanning tree $T$ with
--
--   $$c(G,T)\le(2-\varepsilon)\,\mathrm{STC}(G).$$
--
--   Then $\mathrm{P}=\mathrm{NP}$. Equivalently, for every fixed $\varepsilon\in(0,1)$ there is no polynomial-time $(2-\varepsilon)$-approximation algorithm for spanning tree congestion unless $\mathrm P=\mathrm{NP}$; together with the main theorem this brackets the approximability of the problem between a constant and $\tilde O(n^{2/3})$.
--
--   Differences from the source:
--   - encoding: polynomial-time algorithm; P = NP → a uniform finite-alphabet TM2 evaluator with a polynomial step bound (the mission's machine model); Cook's classes P and NP over the binary alphabet from the published definition CookPvsNP_defs; reason: both are standard polynomial-time models; the classes are the usual ones
--   - generalization: an approximation algorithm on all inputs of spanning tree congestion → the approximation is assumed only on connected simple graphs with n ≥ 2 vertices; reason: a weaker hypothesis gives a stronger implication; graphs on one vertex have only the empty tree
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, Theorem 4.1, PDF/printed p.16; proof pp.16–17

import Definitions.Def_STCSublinear1377_Main_Machine
import Definitions.Def_CookPvsNP_defs
set_option autoImplicit false

namespace STCSublinear1377.Main.Supplement

/-- Theorem 4.1: for every fixed `ε ∈ (0, 1)`, a deterministic polynomial-time `(2 - ε)`-approximation
for spanning tree congestion on connected simple unweighted graphs implies `P = NP`. -/
theorem theorem_4_1 :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      (∃ a : BinaryEvaluator, ∀ n : ℕ, 2 ≤ n → ∀ g : Table n, isInput g →
        let t := outputTable n (a.eval (graphTapeBits g []))
        spanning g t ∧ (congestion g t : ℝ) ≤ (2 - ε) * (stc g : ℝ)) →
      CookPvsNP.P Bool = CookPvsNP.NP Bool := by sorry

end STCSublinear1377.Main.Supplement
