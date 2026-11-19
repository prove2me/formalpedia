-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_zero_anchored_grid_degree
-- name    : QuantumBipartiteTesting.Bipartiteness.zero_anchored_grid_degree
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:54:48.339208+00:00
-- url     : https://prove2.me/theorems/e7b30536-c9f2-4d88-9224-491e936ac38e
-- title:
--   Translated arithmetic-grid degree bound with a zero boundary anchor
-- statement:
--   Fix $\gamma>0$. There is $c_\gamma>0$ such that the following holds for positive integers $C$ and $R\ge2$. Let $Q$ be a real bivariate polynomial satisfying
--
--   $$
--   |Q(X,l)|\le1
--   $$
--
--   at every integer point with $1\le l\le R$, $|X-C|\le R^{3/2}/2$, and $l\mid X$. If
--
--   $$
--   Q(C,0)=0,\qquad |Q(C,1)|\ge\gamma,
--   $$
--
--   then
--
--   $$
--   \deg Q\ge c_\gamma\sqrt R.
--   $$
--
--   This boundary-anchored variant of the translated arithmetic-grid degree estimate applies directly to polynomials retaining the gap's factor of $l$. It replaces the original adjacent-point gap hypothesis by a nonzero value adjacent to a specified zero boundary value.
-- source:
--   Kayal–Sen–Szabó, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf, Lemma 2.12 (translated ACL11 Lemma 4) and §3.5 polynomial argument, pp.11 and 19–20. Boundary-anchored variant derived by the same two-case proof, using the zero factor from Proposition 3.10. Endpoint argument adapted from https://github.com/formalcs/circuit-complexity/releases/tag/release%2F0.2.0, Apache 2.0.

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction
open QuantumBipartiteTesting.Bipartiteness
open scoped BigOperators Classical

theorem QuantumBipartiteTesting.Bipartiteness.zero_anchored_grid_degree : ∀ γ : ℝ, 0 < γ → ∃ c : ℝ, 0 < c ∧
    ∀ C R : ℕ, 0 < C → 2 ≤ R → ∀ Q : Bivariate,
      (∀ X l : ℤ, 1 ≤ l → l ≤ (R:ℤ) →
        |(X:ℝ)-C| ≤ (R:ℝ)^(3/2:ℝ)/2 → l ∣ X → |Eval Q X l| ≤ 1) →
      Eval Q C 0 = 0 → γ ≤ |Eval Q C 1| → c*Real.sqrt R ≤ (Q.totalDegree:ℝ) := by sorry
