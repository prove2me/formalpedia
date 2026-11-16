-- Prove2me | Theorems.Thm_STCSublinear1377_Main_Supplement_theorem_1_4
-- name    : STCSublinear1377.Main.Supplement.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:21:46.817105+00:00
-- url     : https://prove2.me/theorems/5502d641-18eb-4831-9a5e-9c027ce01458
-- title:
--   Theorem 1.4 — Randomized connected min-max multiway cut with both boundary bounds
-- statement:
--   Let $F$ be a graph on $n\ge1$ vertices with positive integer edge weights of total weight $M$, and let $\Gamma$ be a nonempty set of $t$ terminals such that every connected component of $F$ contains a terminal (so that a connected one-terminal partition exists; in particular $F$ may be any connected graph). Let $\mathrm{OPT}$ be the least possible maximum boundary of a connected one-terminal partition. For every $r>0$ there are a randomized polynomial-time algorithm and constants $C_1,C_2>0$, independent of the input, such that on every random tape the algorithm outputs a connected one-terminal partition $\mathcal A$, and with probability at least $1-n^{-r}$ the same output satisfies both
--
--   $$\max_{A\in\mathcal A}b_F(A)\le C_1\sqrt t\,\mathrm{OPT}\,\log^2 n\qquad\text{and}\qquad \max_{A\in\mathcal A}b_F(A)\le C_2\sqrt{M\cdot\mathrm{OPT}}\,\log^{3/2}n .$$
--
--   In particular the algorithm is an $\tilde O(\sqrt t)$-approximation. The edge-sensitive bound is the one used by the simple algorithm of Section 2.
--
--   Differences from the source:
--   - encoding: a graph with positive integer edge weights and prescribed terminals → a WeightedGraph on Fin n whose vertex set is all of Fin n, weights read in binary, terminals a Finset, partitions as terminal labellings; reason: same instances and same partitions
--   - generalization: a graph G with positive integer weights; the proof applies Theorem B.1 to F = G, which is connected → any such graph in which every connected component contains a terminal; reason: these are exactly the instances with a feasible connected one-terminal partition, and connected graphs are among them
--   - reading: a randomized Õ(√t)-approximation whose maximum boundary is Õ(min{√t·OPT, √(M·OPT)}) → for each r > 0 one machine and constants C₁, C₂ chosen before the input; with probability ≥ 1 − n^{−r} the output satisfies maxB ≤ C₁√t·OPT·log²n and maxB ≤ C₂√(M·OPT)·log^{3/2}n; every tape outputs a connected one-terminal partition; reason: these are the explicit bounds and the Markov/repetition amplification stated in the proof on p.20; a bound by a minimum is the same as both bounds
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, Theorem 1.4, PDF/printed p.3; explicit bounds and amplification in its proof, p.20

import Definitions.Def_STCSublinear1377_Main_Supplement_Terminal
set_option autoImplicit false

namespace STCSublinear1377.Main.Supplement

/-- Theorem 1.4 with both explicit bounds of p.20 on the same connected output partition. The input
graph need not be connected; every component must contain a terminal (feasibility). -/
theorem theorem_1_4 :
    ∀ r : ℝ, 0 < r → ∃ a : RandomDataMachine, ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ n : ℕ, 1 ≤ n → ∀ f : WeightedGraph n,
        f.vertices = Finset.univ → f.positive → f.integral →
        ∀ terms : Finset (Fin n), terms.Nonempty →
        (∀ v : Fin n, ∃ s ∈ terms, (tableGraph f.edges).Reachable v s) →
        let input := integerGraphBits f ++ setBits terms
        (∀ tape : Fin (a.tapeLength input) → Bool, ∃ lab : Fin n → Fin n,
          a.output input tape = labelBits lab ∧ IsConnectedLabeling f terms lab) ∧
        dataProbability a input (fun out => ∃ lab : Fin n → Fin n,
          out = labelBits lab ∧ IsConnectedLabeling f terms lab ∧
          maxBoundary f terms lab ≤
            C₁ * Real.sqrt (terms.card : ℝ) * opt f terms * Real.log (n : ℝ) ^ 2 ∧
          maxBoundary f terms lab ≤
            C₂ * Real.sqrt (f.totalWeight * opt f terms) *
              Real.rpow (Real.log (n : ℝ)) (3 / 2 : ℝ)) ≥
          1 - Real.rpow (n : ℝ) (-r) := by sorry

end STCSublinear1377.Main.Supplement
