-- Prove2me | Theorems.Thm_TreewidthApprox_Pushed_restrict_terminal_sep
-- name    : TreewidthApprox.Pushed.restrict_terminal_sep
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:22.595099+00:00
-- url     : https://prove2.me/theorems/9d9eaa2e-77e3-4153-954e-d7479be43c75
-- title:
--   Proof of Lemma 6.5, p. 369 — restricting (L, X, R) to G₁, G₂ gives terminal separations of orders |X ∩ A₁|, |X ∩ A₂|
-- statement:
--   This is the step of the proof of Lemma 6.5 that establishes part (i).
--
--   Let $(A_1, B, A_2)$ and $(L, X, R)$ be two separations of a finite graph $G$. Put
--
--   $$
--   T_L = L \cap B,\quad X_B = X \cap B,\quad T_R = R \cap B,\quad k_1 = |X \cap A_1|,\quad k_2 = |X \cap A_2|,
--   $$
--
--   and for $i = 1, 2$ let $G_i = G[A_i \cup (B \setminus X_B)]$ with terminals $T_L, T_R$. Then:
--
--   1. $\bigl(L \cap (A_1 \cup B),\; X \cap A_1,\; R \cap (A_1 \cup B)\bigr)$ is a terminal separation of $G_1$ of order $k_1$;
--   2. $\bigl(L \cap (A_2 \cup B),\; X \cap A_2,\; R \cap (A_2 \cup B)\bigr)$ is a terminal separation of $G_2$ of order $k_2$;
--   3. $k_1 + k_2 + |X_B| = |X|$.
--
--   The paper phrases items 1–2 as "$X \cap A_1$ and $X \cap A_2$ are terminal separations in $G_1$ and $G_2$", naming each separation by its middle part. Item 3 is the budget identity behind $k_1 + k_2 + |X_B| \le k+1$ when $|X| \le k+1$.
--
--   **Formalization Note** $G_i$ is encoded by its vertex set $A_i \cup (B \setminus X_B)$ (see the definitions file).
-- source:
--   Bodlaender, Drange, Dregi, Fomin, Lokshtanov and Pilipczuk, A c^k n 5-approximation algorithm for treewidth, SIAM J. Comput. 45(2) (2016), p. 369, proof of Lemma 6.5, first paragraph

import Mathlib
import Definitions.Def_TreewidthApprox_Pushed_Setting

namespace TreewidthApprox.Pushed

theorem restrict_terminal_sep {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A₁ B A₂ : Finset V) (hAB : IsSeparation G A₁ B A₂)
    (L X R : Finset V) (hLXR : IsSeparation G L X R) :
    IsTerminalSep G (A₁ ∪ (B \ (X ∩ B))) (L ∩ B) (R ∩ B) (X ∩ A₁).card
        (L ∩ (A₁ ∪ B)) (X ∩ A₁) (R ∩ (A₁ ∪ B)) ∧
      IsTerminalSep G (A₂ ∪ (B \ (X ∩ B))) (L ∩ B) (R ∩ B) (X ∩ A₂).card
        (L ∩ (A₂ ∪ B)) (X ∩ A₂) (R ∩ (A₂ ∪ B)) ∧
      (X ∩ A₁).card + (X ∩ A₂).card + (X ∩ B).card = X.card := by sorry

end TreewidthApprox.Pushed
