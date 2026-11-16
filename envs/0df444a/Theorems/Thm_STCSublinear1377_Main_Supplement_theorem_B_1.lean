-- Prove2me | Theorems.Thm_STCSublinear1377_Main_Supplement_theorem_B_1
-- name    : STCSublinear1377.Main.Supplement.theorem_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:27:29.817053+00:00
-- url     : https://prove2.me/theorems/8539d154-c117-47a8-a2d6-89da8b5390a6
-- title:
--   Theorem B.1 — Connecting a terminal partition with boundary O(√(SB) log t)
-- statement:
--   Let $F$ be a connected graph with positive integer edge weights and let $\mathcal A$ be a partition of $V(F)$ into $t\ge2$ parts, each containing exactly one of $t$ prescribed terminals; the parts need not be connected. Put
--
--   $$B=\max_{A\in\mathcal A}b_F(A),\qquad S=\sum_{A\in\mathcal A}b_F(A).$$
--
--   There are a deterministic polynomial-time algorithm and an absolute constant $C>0$ which, given $F$, the terminals and $\mathcal A$, output a connected one-terminal partition $\mathcal A'$ with
--
--   $$\max_{A\in\mathcal A'}b_F(A)\le C\sqrt{SB}\,\log t .$$
--
--   Applied to the output of a min-max multiway cut algorithm, this yields Theorem 1.4.
--
--   Differences from the source:
--   - encoding: a graph with positive integer edge weights and prescribed terminals → a WeightedGraph on Fin n whose vertex set is all of Fin n, weights read in binary, terminals a Finset, partitions as terminal labellings; reason: same instances and same partitions
--   - reading: O(√(SB) log t) → ≤ C·√(S·B)·log t with one absolute C chosen before the algorithm's inputs; reason: the proof's bound (1 + ln t)(η + 1)B + S/η with η = ⌈√(S/B)⌉ is at most an absolute multiple of √(SB) log t for t ≥ 2
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, Theorem B.1, PDF/printed p.19; proof p.19

import Definitions.Def_STCSublinear1377_Main_Supplement_Terminal
set_option autoImplicit false

namespace STCSublinear1377.Main.Supplement

/-- Theorem B.1: an arbitrary (possibly disconnected) one-terminal partition is turned into a
connected one with maximum boundary `O(√(S B) log t)`, by a deterministic polynomial-time machine. -/
theorem theorem_B_1 :
    ∃ a : BinaryEvaluator, ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, ∀ f : WeightedGraph n,
        f.vertices = Finset.univ → f.positive → f.integral → f.connected →
        ∀ terms : Finset (Fin n), 2 ≤ terms.card →
        ∀ lab : Fin n → Fin n, IsTerminalLabeling f terms lab →
          ∃ lab' : Fin n → Fin n,
            a.eval (integerGraphBits f ++ setBits terms ++ labelBits lab) = labelBits lab' ∧
            IsConnectedLabeling f terms lab' ∧
            maxBoundary f terms lab' ≤
              C * Real.sqrt (sumBoundary f terms lab * maxBoundary f terms lab) *
                Real.log (terms.card : ℝ) := by sorry

end STCSublinear1377.Main.Supplement
