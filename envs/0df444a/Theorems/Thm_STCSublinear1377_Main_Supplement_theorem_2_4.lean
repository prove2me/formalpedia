-- Prove2me | Theorems.Thm_STCSublinear1377_Main_Supplement_theorem_2_4
-- name    : STCSublinear1377.Main.Supplement.theorem_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:24:27.140656+00:00
-- url     : https://prove2.me/theorems/0cccfc92-4066-4299-afa1-a5a6e1a7807e
-- title:
--   Theorem 2.4 — The simple algorithm has approximation ratio Õ(n^{8/9})
-- statement:
--   Let $G$ be a connected simple unweighted graph on $n\ge2$ vertices, $k=\mathrm{STC}(G)$, and consider the algorithm of §2 with $D=4n^{8/9}$: compute the hubs; if $q=n$ return a Chandran–Cheung–Issac tree; if $q=0$ use the Lemma 2.3 routine on $V(G)$; otherwise split $G$ into one-hub regions by exact minimum cuts, split each region minus its hub by Theorem 1.4 on every component with at least two terminals (a one-terminal component is kept), build internal trees by Lemma 2.3, attach them to the hubs, join the regional trees, and return the better of this tree and the Chandran–Cheung–Issac tree. The statement has two parts.
--
--   1. *Analysis.* For all constants $C_1,C_2>0$ there is $C>0$ such that every run of the algorithm on every such $G$ in which every Theorem 1.4 call meets its guarantee with constant $C_1$ and every Lemma 2.3 call meets its guarantee with constant $C_2$ returns a tree $T$ with
--
--   $$\frac{c(G,T)}{k}\le C\,n^{8/9}\log^3 n .$$
--
--   2. *Realization.* For every $r>0$ there are a randomized polynomial-time algorithm and constants $C_1,C_2>0$ such that on every random tape the output is the tree of a run of the algorithm, and with probability at least $1-n^{-r}$ it is the tree of a run in which all calls meet their guarantees with constants $C_1,C_2$.
--
--   Together the two parts give a randomized polynomial-time $O(n^{8/9}\log^3 n)$-approximation realized by this algorithm. The explicit $\log^3 n$ combines the $\log^{3/2}n$ losses of Theorem 1.4 and Lemma 2.3.
--
--   Differences from the source:
--   - reading: the approximation ratio of the above described randomized algorithm is Õ(n^{8/9}) → an analysis clause (every run whose subroutine calls meet their guarantees with any constants C₁, C₂ has ratio ≤ C·n^{8/9}·log³n) and a realization clause (one randomized polynomial-time machine per r > 0 whose every output is a run's tree, and with probability ≥ 1 − n^{−r} a successful run's tree); reason: the randomized subroutines are specified in the source only by their guarantees; the log³n is the explicit form of the tilde obtained from (2.1)–(2.3) and p.20
--   - encoding: the Chandran–Cheung–Issac tree and the outputs of the Theorem 1.4 and Lemma 2.3 calls → any spanning tree with congestion ≤ 8√(mn), and arbitrary outputs of the right format whose guarantees enter through the success predicate; reason: Proposition 1.2 and the two subroutines are used in the proof only through these guarantees
--   - generalization: Theorem 1.4 calls meeting the guarantee with logarithms of the component order → success requires the guarantee with logarithms of n = |V(G)|; reason: this is a weaker requirement on each call, so every run whose calls meet the source guarantee is covered
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, Theorem 2.4, PDF/printed p.5; algorithm steps (1)–(4) p.5, (2.1)–(2.3) pp.4–5; logarithms of Theorem 1.4 from p.20

import Definitions.Def_STCSublinear1377_Main_Supplement_Section2
set_option autoImplicit false

namespace STCSublinear1377.Main.Supplement

/-- Theorem 2.4. First clause: every run of steps (1)–(4) whose subroutine calls meet their
guarantees has ratio `O(n^{8/9} log³ n)`. Second clause: the algorithm is realized by a randomized
polynomial-time machine that always returns the tree of a legal run, and with probability at least
`1 - n^{-r}` the tree of a run whose calls all succeed. -/
theorem theorem_2_4 :
    (∀ C₁ C₂ : ℝ, 0 < C₁ → 0 < C₂ → ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 2 ≤ n → ∀ g : Table n, isInput g →
      ∀ x : Section2Run g, x.valid → x.succeeds C₁ C₂ →
        (congestion g x.output : ℝ) / (stc g : ℝ) ≤
          C * Real.rpow (n : ℝ) (8 / 9 : ℝ) * Real.log (n : ℝ) ^ 3) ∧
    (∀ r : ℝ, 0 < r → ∃ a : RandomGraphMachine, ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ n : ℕ, 2 ≤ n → ∀ g : Table n, isInput g →
        (∀ tape : Fin (a.tapeLength n) → Bool,
          (a.output g tape).length = n * n ∧
          ∃ x : Section2Run g, x.valid ∧ x.output = outputTable n (a.output g tape)) ∧
        tapeProbability a n (fun tape => ∃ x : Section2Run g, x.valid ∧
          x.succeeds C₁ C₂ ∧ x.output = outputTable n (a.output g tape)) ≥
          1 - Real.rpow (n : ℝ) (-r)) := by sorry

end STCSublinear1377.Main.Supplement
