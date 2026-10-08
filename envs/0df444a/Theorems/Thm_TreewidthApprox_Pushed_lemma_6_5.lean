-- Prove2me | Theorems.Thm_TreewidthApprox_Pushed_lemma_6_5
-- name    : TreewidthApprox.Pushed.lemma_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:43.26498+00:00
-- url     : https://prove2.me/theorems/ec8ca385-f908-48b5-b723-c34ba1a74114
-- title:
--   Lemma 6.5 — pushed terminal separations around a ¾-balanced separation glue to a separation of order k+1 with sides ≤ ⅞|V(G)| + (|B|+(k+1))/2
-- statement:
--   Let $G$ be a finite graph of treewidth at most $k$, and let $(A_1, B, A_2)$ be a separation of $G$ (a partition of $V(G)$ with no edge between $A_1$ and $A_2$) such that $|A_1|, |A_2| \le \tfrac34 |V(G)|$. Then there exist a partition $(T_L, X_B, T_R)$ of $B$ and integers $k_1, k_2 \ge 0$ with $k_1 + k_2 + |X_B| \le k+1$ such that, writing
--
--   $$
--   G_1 = G[A_1 \cup (B \setminus X_B)], \qquad G_2 = G[A_2 \cup (B \setminus X_B)],
--   $$
--
--   both with terminals $T_L, T_R$:
--
--   1. $G_1$ has a terminal separation of order $k_1$, and $G_2$ has a terminal separation of order $k_2$;
--   2. for every left-pushed terminal separation $(L_1, X_1, R_1)$ of $G_1$ of order $k_1$ and every right-pushed terminal separation $(L_2, X_2, R_2)$ of $G_2$ of order $k_2$, the triple $(L_1 \cup T_L \cup L_2,\ X_1 \cup X_B \cup X_2,\ R_1 \cup T_R \cup R_2)$ is a terminal separation of $G$ (terminals $T_L, T_R$) of order at most $k+1$, and
--   $$
--   |L_1 \cup T_L \cup L_2|,\ |R_1 \cup T_R \cup R_2| \;\le\; \tfrac78|V(G)| + \frac{|B| + (k+1)}{2}.
--   $$
--
--   The lemma converts the search for a small balanced separator into two maximization problems (a left-pushed and a right-pushed separation), each solvable by dynamic programming over a tree decomposition; this is how the paper's data structure answers its balanced-separator query.
--
--   **Formalization Note** The printed bound reads $\tfrac78|V(G)| + \tfrac{|X| + (k+1)}{2}$, where $X$ is not bound in the statement; the proof derives the bound with $|B|$, which is stated here. Part (i) is kept so that the pushed separations of (ii) exist and (ii) is not vacuous. The induced subgraphs $G_i$ are encoded by their vertex sets; treewidth at most $k$ is `RobertsonSeymour1986.GM5.TreewidthLE G k`; size bounds are over the reals.
-- source:
--   Bodlaender, Drange, Dregi, Fomin, Lokshtanov and Pilipczuk, A c^k n 5-approximation algorithm for treewidth, SIAM J. Comput. 45(2) (2016), p. 369, Lemma 6.5 (proof pp. 369–370)

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Definitions.Def_TreewidthApprox_Pushed_Setting

namespace TreewidthApprox.Pushed

theorem lemma_6_5 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (k : ℕ) (htw : RobertsonSeymour1986.GM5.TreewidthLE G k)
    (A₁ B A₂ : Finset V) (hsep : IsSeparation G A₁ B A₂)
    (hA₁ : (A₁.card : ℝ) ≤ 3 / 4 * Fintype.card V) (hA₂ : (A₂.card : ℝ) ≤ 3 / 4 * Fintype.card V) :
    ∃ (TL XB TR : Finset V) (k₁ k₂ : ℕ),
      IsPartition3 B TL XB TR ∧ k₁ + k₂ + XB.card ≤ k + 1 ∧
      (∃ L X R : Finset V, IsTerminalSep G (A₁ ∪ (B \ XB)) TL TR k₁ L X R) ∧
      (∃ L X R : Finset V, IsTerminalSep G (A₂ ∪ (B \ XB)) TL TR k₂ L X R) ∧
      ∀ L₁ X₁ R₁ L₂ X₂ R₂ : Finset V,
        IsLeftPushed G (A₁ ∪ (B \ XB)) TL TR k₁ L₁ X₁ R₁ →
        IsRightPushed G (A₂ ∪ (B \ XB)) TL TR k₂ L₂ X₂ R₂ →
        IsTerminalSep G Finset.univ TL TR (k + 1) (L₁ ∪ TL ∪ L₂) (X₁ ∪ XB ∪ X₂) (R₁ ∪ TR ∪ R₂) ∧
        ((L₁ ∪ TL ∪ L₂).card : ℝ) ≤ 7 / 8 * Fintype.card V + ((B.card : ℝ) + (k + 1)) / 2 ∧
        ((R₁ ∪ TR ∪ R₂).card : ℝ) ≤ 7 / 8 * Fintype.card V + ((B.card : ℝ) + (k + 1)) / 2 := by sorry

end TreewidthApprox.Pushed
