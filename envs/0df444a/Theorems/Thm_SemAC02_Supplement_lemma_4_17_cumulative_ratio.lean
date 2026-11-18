-- Prove2me | Theorems.Thm_SemAC02_Supplement_lemma_4_17_cumulative_ratio
-- name    : SemAC02.Supplement.lemma_4_17_cumulative_ratio
-- status  : Proved
-- author  : @Henry Yuen
-- created : 2026-11-17T19:31:48.221887+00:00
-- url     : https://prove2.me/theorems/eed56479-b5e8-4068-9bbb-52e6dbc3fb33
-- title:
--   Lemma 4.17: cumulative binomial counts near half the variables
-- statement:
--   Let $0<\varepsilon\leq1/256$, let $n$ be a nonnegative integer with $n\geq16/\varepsilon^2$, and put $k=\lfloor(1/2-\varepsilon)n\rfloor$. For a nonnegative integer $u$, write $H_n(u)=\sum_{j=0}^{\min(u,n)}\binom nj$, the dimension of the Boolean polynomial space of degree at most $u$.
--
--   For every nonnegative integer $a\leq\varepsilon n/2$,
--
--   $$
--   \frac{H_n(k-a)}{H_n(k)}\geq\exp(-128\varepsilon a).
--   $$
--
--   This controls the loss in the degree filtration near half the variables and gives the explicit exponent in the semantic Frege size bound of Corollary 4.18.
--
--   **Formalization Note** Natural-number subtraction is exact here: the hypotheses imply $a\leq k$. The dimension function uses the mission's existing definition.
-- source:
--   Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, Lemma 4.17, equation (11), printed pp.36–37, https://www.doc.ic.ac.uk/~itzamere/Reslin_Simplification.pdf. Checked against the public manuscript saved in sources/Hard_Instances_Semantic.pdf, whose hash differs from the mission-pinned manuscript.

import Mathlib
import Definitions.Def_SemAC02_Ble

theorem SemAC02.Supplement.lemma_4_17_cumulative_ratio (n : ℕ) (ε : ℝ) (hε₀ : 0 < ε) (hε : ε ≤ 1/256)
    (hn : 16/ε^2 ≤ (n : ℝ)) (a : ℕ) (ha : (a : ℝ) ≤ ε*n/2) :
    Real.exp (-(128*ε*(a : ℝ))) ≤
      (SemAC02.Hn n (⌊(1/2-ε)*(n : ℝ)⌋₊-a) : ℝ) /
        (SemAC02.Hn n ⌊(1/2-ε)*(n : ℝ)⌋₊ : ℝ) := by sorry
