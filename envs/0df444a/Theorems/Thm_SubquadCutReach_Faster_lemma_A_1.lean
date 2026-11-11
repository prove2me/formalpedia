-- Prove2me | Theorems.Thm_SubquadCutReach_Faster_lemma_A_1
-- name    : SubquadCutReach.Faster.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T17:03:38.770843+00:00
-- url     : https://prove2.me/theorems/f547d53f-66e3-47c3-8608-23bc10900c43
-- title:
--   Lemma A.1 — Weighted neighbour sums
-- statement:
--   For a vertex $v$, a known set $X\subseteq V\setminus\{v\}$ and known signed weights $a_w\in[-1,1]$, let $S_v=\sum_{w\in X}c_{vw}a_w$. For every fixed $c>0$, uniform deterministic programs compute estimates satisfying
--
--   $$|\widetilde S_v-S_v|\le n^{-c},\qquad Q_v\le C_cL(n),\qquad Q_{\rm all}\le C_cnL(n).$$
--
--   The all-vertex result allows independently supplied candidate sets and weight rows. The single-vertex output equals the sum after signed binary truncation to $(\lceil c\rceil+2)(\lfloor\log_2(n+2)\rfloor+1)$ digits. Constants depend on $c$ but precede every graph and weight input. This provides the charged approximate loss evaluations needed for averaging.
--
--   Differences from the source:
--   - encoding: finite labelled oracle inputs and O or Õ bounds → Fin n, finite rational-literal oracle programs, charged queries and outer uniform positive constants; reason: relabeling and an operational cost semantics preserve the source input domain; nontermination has infinite cost
--   - encoding: O(log n) signed truncation digits for any fixed c → (ceil c+2)(floor log₂(n+2)+1) digits supplied as a known precision parameter; reason: the source truncation proof then gives total error at most n^(-c), with coefficients independent of graph and weights
--   - generalization: the single-vertex sum is approximated to additive error n^(-c) → the single-vertex output additionally equals exactly the weighted sum of the truncated weights; reason: an extra conclusion that the source proof establishes; together with the error bound it implies the claim of the source
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), p. 20, Lemma A.1 (PDF p. 22)

import Definitions.Def_SubquadCutReach_Faster_Tasks

set_option autoImplicit false

namespace SubquadCutReach.Faster

theorem lemma_A_1 :
    ∃ P Pall : Program, Admissible P ∧ Deterministic P ∧ Admissible Pall ∧ Deterministic Pall ∧
    ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧
      (∀ (n : ℕ) (H : SimpleGraph (Fin n)) (v : Fin n) (X : Finset (Fin n))
          (a : Fin n → ℝ), v ∉ X → (∀ w, -1 ≤ a w ∧ a w ≤ 1) →
        RunsWithin P (cut H) (weightInput v X a (weightDigits n c))
          (fun m => m 0 = weighted H v X (fun w => trunc (weightDigits n c) (a w)) ∧
            |m 0 - weighted H v X a| ≤ (n:ℝ)^(-c)) (C*L n)) ∧
      (∀ (n : ℕ) (H : SimpleGraph (Fin n)) (X : Fin n → Finset (Fin n))
          (a : Fin n → Fin n → ℝ), (∀ v, v ∉ X v) →
          (∀ v w, -1 ≤ a v w ∧ a v w ≤ 1) →
        RunsWithin Pall (cut H) (weightMatrixInput X a (weightDigits n c))
          (fun m => ∀ v, |m v.val - weighted H v (X v) (a v)| ≤ (n:ℝ)^(-c))
          (C*n*L n)) := by sorry

end SubquadCutReach.Faster
