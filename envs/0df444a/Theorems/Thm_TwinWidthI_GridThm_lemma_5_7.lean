-- Prove2me | Theorems.Thm_TwinWidthI_GridThm_lemma_5_7
-- name    : TwinWidthI.GridThm.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:14.529154+00:00
-- url     : https://prove2.me/theorems/cb1e4e21-3c53-4b7c-a437-0642180c0105
-- title:
--   Lemma 5.7 — a t-mixed free matrix has a division sequence of mixed value at most 2c_t
-- statement:
--   Let $t\ge1$, $c_t=\tfrac83(t+1)^22^{4t}$, and let $M$ be an $n\times m$ matrix over a finite alphabet with $n,m\ge1$. If $M$ is $t$-mixed free, then $M$ has a *division sequence* $(\mathcal R^0,\mathcal C^0),\dots,(\mathcal R^N,\mathcal C^N)$ — a contraction sequence from the finest to the coarsest partition, each step fusing two row parts or two column parts, in which every partition is a division — such that every division in it has mixed value at most $2c_t$:
--
--   $$\operatorname{mv}(\mathcal R^i,\mathcal C^i)\le 2c_t\qquad(0\le i\le N).$$
--
--   The division sequence is not yet a contraction sequence of small error value, but it is the frame on which the proof of Theorem 5.4 builds one.
--
--   **Formalization Note** Since mixed values are integers, "at most $2c_t$" is stated as at most $\lfloor 2c_t\rfloor$. Added hypotheses: $t\ge1$ and $n,m\ge1$, matching Theorem 5.4. The paper's application of Theorem 5.3 in the proof has an off-by-one when the number of row and column parts is equal and odd; the statement is unaffected.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:20, Lemma 5.7

import Mathlib
import Definitions.Def_TwinWidthI_GridThm_Setting

namespace TwinWidthI.GridThm

/-- Lemma 5.7, p. 3:20: every `t`-mixed free matrix has a division sequence in which every
division has mixed value at most `2 c_t`. -/
theorem lemma_5_7 {A : Type*} [Fintype A] (n m t : ℕ) (ht : 1 ≤ t) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (M : Matrix (Fin n) (Fin m) A) (hfree : MixedFree M t) :
    ∃ (N : ℕ) (R : Fin (N + 1) → Finpartition (Finset.univ : Finset (Fin n)))
      (C : Fin (N + 1) → Finpartition (Finset.univ : Finset (Fin m))),
      R 0 = ⊥ ∧ C 0 = ⊥ ∧ (R (Fin.last N)).parts.card ≤ 1 ∧ (C (Fin.last N)).parts.card ≤ 1 ∧
      (∀ i : Fin N, (TwinWidthI.BoolWidth.IsMergeStep (R i.castSucc) (R i.succ) ∧ C i.succ = C i.castSucc) ∨
                    (R i.succ = R i.castSucc ∧ TwinWidthI.BoolWidth.IsMergeStep (C i.castSucc) (C i.succ))) ∧
      ∀ i, IsDivision (R i) ∧ IsDivision (C i) ∧
        MixedValueLE M (R i) (C i) ⌊2 * cMT t⌋₊ := by sorry

end TwinWidthI.GridThm
