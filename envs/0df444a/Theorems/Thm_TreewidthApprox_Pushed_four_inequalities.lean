-- Prove2me | Theorems.Thm_TreewidthApprox_Pushed_four_inequalities
-- name    : TreewidthApprox.Pushed.four_inequalities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:31:36.717785+00:00
-- url     : https://prove2.me/theorems/d8c55dd7-c332-4a4b-bfe2-179fcb1affdc
-- title:
--   Proof of Lemma 6.5, pp. 369–370 — the four inequalities for L ∩ Aᵢ and R ∩ Aᵢ
-- statement:
--   Let $G$ be a finite graph and $k \ge 0$ an integer. Let $(A_1, B, A_2)$ be a separation of $G$ with $|A_1|, |A_2| \le \tfrac34|V(G)|$, and let $(L, X, R)$ be a separation of $G$ with $|L|, |R| \le \tfrac23 |V(G)|$ and $|X| \le k+1$. Then
--
--   $$
--   \begin{aligned}
--   |L \cap A_1| + |L \cap A_2| + |B| &\ge \tfrac13|V(G)| - (k+1),\\
--   |R \cap A_1| + |R \cap A_2| + |B| &\ge \tfrac13|V(G)| - (k+1),\\
--   |L \cap A_1| + |R \cap A_1| + (k+1) &\ge \tfrac14|V(G)| - |B|,\\
--   |L \cap A_2| + |R \cap A_2| + (k+1) &\ge \tfrac14|V(G)| - |B|.
--   \end{aligned}
--   $$
--
--   These four lower bounds on the "quadrants" $L \cap A_i$, $R \cap A_i$ are the counting core of the proof of Lemma 6.5; the dichotomy that follows uses only them.
--
--   **Formalization Note** The page says the two separations are "$\tfrac14$- and $\tfrac13$-balanced"; this is a slip for $\tfrac34$ and $\tfrac23$, which are the hypotheses of Lemma 6.5 and of the folklore separation, and which are the ones stated here. All quantities are compared as real numbers, since the right-hand sides may be negative.
-- source:
--   Bodlaender, Drange, Dregi, Fomin, Lokshtanov and Pilipczuk, A c^k n 5-approximation algorithm for treewidth, SIAM J. Comput. 45(2) (2016), pp. 369–370, proof of Lemma 6.5, second paragraph (four bulleted inequalities)

import Mathlib
import Definitions.Def_TreewidthApprox_Pushed_Setting

namespace TreewidthApprox.Pushed

theorem four_inequalities {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (k : ℕ) (A₁ B A₂ : Finset V) (hAB : IsSeparation G A₁ B A₂)
    (hA₁ : (A₁.card : ℝ) ≤ 3 / 4 * Fintype.card V) (hA₂ : (A₂.card : ℝ) ≤ 3 / 4 * Fintype.card V)
    (L X R : Finset V) (hLXR : IsSeparation G L X R) (hX : X.card ≤ k + 1)
    (hL : (L.card : ℝ) ≤ 2 / 3 * Fintype.card V) (hR : (R.card : ℝ) ≤ 2 / 3 * Fintype.card V) :
    ((L ∩ A₁).card : ℝ) + (L ∩ A₂).card + B.card ≥ 1 / 3 * Fintype.card V - (k + 1) ∧
      ((R ∩ A₁).card : ℝ) + (R ∩ A₂).card + B.card ≥ 1 / 3 * Fintype.card V - (k + 1) ∧
      ((L ∩ A₁).card : ℝ) + (R ∩ A₁).card + (k + 1) ≥ 1 / 4 * Fintype.card V - B.card ∧
      ((L ∩ A₂).card : ℝ) + (R ∩ A₂).card + (k + 1) ≥ 1 / 4 * Fintype.card V - B.card := by sorry

end TreewidthApprox.Pushed
