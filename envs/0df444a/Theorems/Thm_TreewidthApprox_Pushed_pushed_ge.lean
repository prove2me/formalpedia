-- Prove2me | Theorems.Thm_TreewidthApprox_Pushed_pushed_ge
-- name    : TreewidthApprox.Pushed.pushed_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:28.013431+00:00
-- url     : https://prove2.me/theorems/e2a4ba62-ce94-415f-ae79-c7cf6c6b99e0
-- title:
--   Proof of Lemma 6.5, p. 370 — pushed separations dominate the restriction of (L, X, R): |L₁ ∩ A₁| ≥ |L ∩ A₁|, |R₂ ∩ A₂| ≥ |R ∩ A₂|
-- statement:
--   Let $(A_1, B, A_2)$ and $(L, X, R)$ be two separations of a finite graph $G$, and set, as in the proof of Lemma 6.5,
--
--   $$
--   T_L = L \cap B,\quad X_B = X \cap B,\quad T_R = R \cap B,\quad k_1 = |X \cap A_1|,\quad k_2 = |X \cap A_2|,
--   $$
--
--   with $G_i = G[A_i \cup (B \setminus X_B)]$ carrying terminals $T_L, T_R$. Then
--
--   1. every left-pushed terminal separation $(L_1, X_1, R_1)$ of $G_1$ of order $k_1$ satisfies $|L_1 \cap A_1| \ge |L \cap A_1|$;
--   2. every right-pushed terminal separation $(L_2, X_2, R_2)$ of $G_2$ of order $k_2$ satisfies $|R_2 \cap A_2| \ge |R \cap A_2|$.
--
--   Together with the dichotomy (in the case $|L \cap A_1|, |R \cap A_2| \ge \varepsilon$) this gives $|L_1 \cap A_1|, |R_2 \cap A_2| \ge \varepsilon$, which bounds the sides of the glued separation in Lemma 6.5.
--
--   **Formalization Note** $G_i$ is encoded by its vertex set $A_i \cup (B \setminus X_B)$; pushedness compares with all terminal separations of $G_i$ of order at most $k_i$ with the same terminals.
-- source:
--   Bodlaender, Drange, Dregi, Fomin, Lokshtanov and Pilipczuk, A c^k n 5-approximation algorithm for treewidth, SIAM J. Comput. 45(2) (2016), p. 370, proof of Lemma 6.5, last paragraph

import Mathlib
import Definitions.Def_TreewidthApprox_Pushed_Setting

namespace TreewidthApprox.Pushed

theorem pushed_ge {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A₁ B A₂ : Finset V) (hAB : IsSeparation G A₁ B A₂)
    (L X R : Finset V) (hLXR : IsSeparation G L X R) :
    (∀ L₁ X₁ R₁ : Finset V,
        IsLeftPushed G (A₁ ∪ (B \ (X ∩ B))) (L ∩ B) (R ∩ B) (X ∩ A₁).card L₁ X₁ R₁ →
        (L ∩ A₁).card ≤ (L₁ ∩ A₁).card) ∧
      (∀ L₂ X₂ R₂ : Finset V,
        IsRightPushed G (A₂ ∪ (B \ (X ∩ B))) (L ∩ B) (R ∩ B) (X ∩ A₂).card L₂ X₂ R₂ →
        (R ∩ A₂).card ≤ (R₂ ∩ A₂).card) := by sorry

end TreewidthApprox.Pushed
