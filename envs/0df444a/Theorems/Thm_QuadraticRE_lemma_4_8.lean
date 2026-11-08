-- Prove2me | Theorems.Thm_QuadraticRE_lemma_4_8
-- name    : QuadraticRE.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:11:26.014241+00:00
-- url     : https://prove2.me/theorems/2b241513-1dbf-4279-ac29-d7ef747b839e
-- title:
--   Lemma 4.8 — recursive reconstruction rules
-- statement:
--   Let $j\ge0$, $S\subseteq[4^{j+1}]$, and for each child $\nu\in[4]$ let $S_\nu\subseteq[4^j]$ be the selected leaves of child block $\nu$, numbered within the block, and $e_{X,\nu}=\mathrm{Auth}^j_X(S_\nu)$. Then
--   $$\mathrm{Auth}^{j+1}_A(S)=(e_{A,1}\vee e_{A,2})\wedge(e_{A,3}\vee e_{A,4}),\qquad \mathrm{Auth}^{j+1}_C(S)=(e_{C,1}\wedge e_{C,2})\vee(e_{C,3}\wedge e_{C,4}).$$
--
--   This turns the reconstruction probabilities into the recurrences of Lemma 4.9.
--
--   Differences from the source:
--   - encoding: indicator equations Auth = Boolean formula, children 1–4 → equivalences of propositions, children numbered 0–3; reason: Lean convention; same statement
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), Lemma 4.8, p.26

import Mathlib
import Definitions.Def_QuadraticRE_Auth

namespace QuadraticRE

/-- Lemma 4.8 of Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), p.26: the recursive reconstruction rules, as equivalences of the
property of Definition 4.5. -/
theorem lemma_4_8 (j : ℕ) (S : Finset (Fin (4 ^ (j + 1)))) :
    (Auth .A (j + 1) S ↔
      (Auth .A j (block S 0) ∨ Auth .A j (block S 1)) ∧
        (Auth .A j (block S 2) ∨ Auth .A j (block S 3))) ∧
    (Auth .C (j + 1) S ↔
      (Auth .C j (block S 0) ∧ Auth .C j (block S 1)) ∨
        (Auth .C j (block S 2) ∧ Auth .C j (block S 3))) := by sorry

end QuadraticRE
