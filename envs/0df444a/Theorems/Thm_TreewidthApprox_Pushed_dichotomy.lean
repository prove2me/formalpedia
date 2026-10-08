-- Prove2me | Theorems.Thm_TreewidthApprox_Pushed_dichotomy
-- name    : TreewidthApprox.Pushed.dichotomy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:52.345327+00:00
-- url     : https://prove2.me/theorems/2599ea4f-e86e-4650-baf4-7f8bf7173dd7
-- title:
--   Proof of Lemma 6.5, p. 370 — either |L ∩ A₁|, |R ∩ A₂| ≥ ε or |L ∩ A₂|, |R ∩ A₁| ≥ ε, ε = ⅛|V(G)| − (|B|+(k+1))/2
-- statement:
--   Let $G$ be a finite graph and $k \ge 0$ an integer. Let $(A_1, B, A_2)$ be a separation of $G$ with $|A_1|, |A_2| \le \tfrac34|V(G)|$, and let $(L, X, R)$ be a separation of $G$ with $|L|, |R| \le \tfrac23 |V(G)|$ and $|X| \le k+1$. Write
--
--   $$
--   \varepsilon = \tfrac18|V(G)| - \frac{|B| + (k+1)}{2}.
--   $$
--
--   Then at least one of the following holds:
--
--   1. $|L \cap A_1| \ge \varepsilon$ and $|R \cap A_2| \ge \varepsilon$;
--   2. $|L \cap A_2| \ge \varepsilon$ and $|R \cap A_1| \ge \varepsilon$.
--
--   In the proof of Lemma 6.5 this lets one assume, after possibly exchanging the roles of $L$ and $R$, that $L$ meets $A_1$ and $R$ meets $A_2$ in at least $\varepsilon$ vertices each; that is what bounds the sides of the glued separation by $|V(G)| - \varepsilon$.
--
--   **Formalization Note** $\varepsilon$ is a real number and may be negative (then the claim is trivial); all comparisons are over the reals.
-- source:
--   Bodlaender, Drange, Dregi, Fomin, Lokshtanov and Pilipczuk, A c^k n 5-approximation algorithm for treewidth, SIAM J. Comput. 45(2) (2016), p. 370, proof of Lemma 6.5, the claim after the four inequalities

import Mathlib
import Definitions.Def_TreewidthApprox_Pushed_Setting

namespace TreewidthApprox.Pushed

theorem dichotomy {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (k : ℕ) (A₁ B A₂ : Finset V) (hAB : IsSeparation G A₁ B A₂)
    (hA₁ : (A₁.card : ℝ) ≤ 3 / 4 * Fintype.card V) (hA₂ : (A₂.card : ℝ) ≤ 3 / 4 * Fintype.card V)
    (L X R : Finset V) (hLXR : IsSeparation G L X R) (hX : X.card ≤ k + 1)
    (hL : (L.card : ℝ) ≤ 2 / 3 * Fintype.card V) (hR : (R.card : ℝ) ≤ 2 / 3 * Fintype.card V) :
    ((1 / 8 * (Fintype.card V : ℝ) - ((B.card : ℝ) + (k + 1)) / 2) ≤ (L ∩ A₁).card ∧
        (1 / 8 * (Fintype.card V : ℝ) - ((B.card : ℝ) + (k + 1)) / 2) ≤ (R ∩ A₂).card) ∨
      ((1 / 8 * (Fintype.card V : ℝ) - ((B.card : ℝ) + (k + 1)) / 2) ≤ (L ∩ A₂).card ∧
        (1 / 8 * (Fintype.card V : ℝ) - ((B.card : ℝ) + (k + 1)) / 2) ≤ (R ∩ A₁).card) := by sorry

end TreewidthApprox.Pushed
