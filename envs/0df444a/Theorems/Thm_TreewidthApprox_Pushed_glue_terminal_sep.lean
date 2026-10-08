-- Prove2me | Theorems.Thm_TreewidthApprox_Pushed_glue_terminal_sep
-- name    : TreewidthApprox.Pushed.glue_terminal_sep
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:36.237096+00:00
-- url     : https://prove2.me/theorems/52d7bd5e-3220-4ed9-8ea7-366f12861827
-- title:
--   Lemma 6.5 (ii), p. 369 — a left-pushed and a right-pushed terminal separation glue to a terminal separation of G of order ≤ k+1
-- statement:
--   This is the first assertion of Lemma 6.5 (ii).
--
--   Let $(A_1, B, A_2)$ be a separation of a finite graph $G$, let $(T_L, X_B, T_R)$ be a partition of $B$, and let $k, k_1, k_2 \ge 0$ be integers with $k_1 + k_2 + |X_B| \le k + 1$. Let $G_1 = G[A_1 \cup (B \setminus X_B)]$ and $G_2 = G[A_2 \cup (B \setminus X_B)]$, both with terminals $T_L, T_R$. If $(L_1, X_1, R_1)$ is a left-pushed terminal separation of $G_1$ of order $k_1$ and $(L_2, X_2, R_2)$ is a right-pushed terminal separation of $G_2$ of order $k_2$, then
--
--   $$
--   (L_1 \cup T_L \cup L_2,\; X_1 \cup X_B \cup X_2,\; R_1 \cup T_R \cup R_2)
--   $$
--
--   is a terminal separation of $G$ (with terminals $T_L, T_R$) of order at most $k+1$.
--
--   The conclusion in fact holds for any terminal separations of $G_1$ and $G_2$ of orders $k_1$ and $k_2$; pushedness is only needed for the size bounds of Lemma 6.5. The statement keeps the paper's hypotheses.
--
--   **Formalization Note** $G_i$ is encoded by its vertex set; a terminal separation of $G$ itself is one with vertex set $W = V(G)$.
-- source:
--   Bodlaender, Drange, Dregi, Fomin, Lokshtanov and Pilipczuk, A c^k n 5-approximation algorithm for treewidth, SIAM J. Comput. 45(2) (2016), p. 369, Lemma 6.5 (ii), first assertion

import Mathlib
import Definitions.Def_TreewidthApprox_Pushed_Setting

namespace TreewidthApprox.Pushed

theorem glue_terminal_sep {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A₁ B A₂ : Finset V) (hAB : IsSeparation G A₁ B A₂)
    (TL XB TR : Finset V) (hpart : IsPartition3 B TL XB TR)
    (k k₁ k₂ : ℕ) (hbudget : k₁ + k₂ + XB.card ≤ k + 1)
    (L₁ X₁ R₁ L₂ X₂ R₂ : Finset V)
    (h₁ : IsLeftPushed G (A₁ ∪ (B \ XB)) TL TR k₁ L₁ X₁ R₁)
    (h₂ : IsRightPushed G (A₂ ∪ (B \ XB)) TL TR k₂ L₂ X₂ R₂) :
    IsTerminalSep G Finset.univ TL TR (k + 1) (L₁ ∪ TL ∪ L₂) (X₁ ∪ XB ∪ X₂) (R₁ ∪ TR ∪ R₂) := by sorry

end TreewidthApprox.Pushed
