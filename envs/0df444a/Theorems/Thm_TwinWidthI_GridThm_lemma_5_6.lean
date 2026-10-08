-- Prove2me | Theorems.Thm_TwinWidthI_GridThm_lemma_5_6
-- name    : TwinWidthI.GridThm.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:04.309481+00:00
-- url     : https://prove2.me/theorems/12a2e6bd-3b1f-469d-83ae-197ea180951f
-- title:
--   Lemma 5.6 — fusing two consecutive row parts does not increase the mixed value of C
-- statement:
--   Let $M$ be an $n\times m$ matrix over a finite alphabet, $\mathcal R$ a row-division of $M$ (every part consists of consecutive rows), and $C$ a set of consecutive columns. Let $X,X'\in\mathcal R$ be consecutive parts, i.e. the last row of $X$ is immediately followed by the first row of $X'$, and let $\mathcal R'$ be the row-division obtained by replacing $X$ and $X'$ by $X\cup X'$. Then the mixed value of $C$ does not increase:
--
--   $$\operatorname{mv}(C,\mathcal R')\ \le\ \operatorname{mv}(C,\mathcal R),$$
--
--   where $\operatorname{mv}(C,\mathcal R)$ is the number of mixed zones $R_i\cap C$ plus the number of mixed cuts of $C$ on $\mathcal R$.
--
--   This monotonicity is what lets the greedy fusion procedure of Lemma 5.7 keep the mixed value of every column part under control while fusing row parts.
--
--   **Formalization Note** "Consecutive" is stated as: there are $a\in X$, $b\in X'$ with $a=\max X$, $b=\min X'$ and $b=a+1$. $\mathcal R'$ is any `Finpartition` whose parts are those of $\mathcal R$ with $X,X'$ replaced by $X\cup X'$.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:20, Lemma 5.6

import Mathlib
import Definitions.Def_TwinWidthI_GridThm_Setting

namespace TwinWidthI.GridThm

/-- Lemma 5.6, p. 3:20: fusing two consecutive parts `X`, `X'` of a row-division `R` into one part
(giving `R'`) does not increase the mixed value of a set `C` of consecutive columns on the
row-division. -/
theorem lemma_5_6 {A : Type*} [Fintype A] {n m : ℕ} (M : Matrix (Fin n) (Fin m) A)
    (R R' : Finpartition (Finset.univ : Finset (Fin n))) (hR : IsDivision R)
    (C : Finset (Fin m)) (hC : IsIntervalSet C)
    (X X' : Finset (Fin n)) (hX : X ∈ R.parts) (hX' : X' ∈ R.parts)
    (hcons : ∃ a ∈ X, ∃ b ∈ X', (∀ x ∈ X, x ≤ a) ∧ (∀ y ∈ X', b ≤ y) ∧ (a : ℕ) + 1 = b)
    (hR' : R'.parts = insert (X ∪ X') ((R.parts.erase X).erase X')) :
    mixedValueRow M R' C ≤ mixedValueRow M R C := by sorry

end TwinWidthI.GridThm
