-- Prove2me | Theorems.Thm_SparseReznick_Psatz_lemma_3_5
-- name    : SparseReznick.Psatz.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:47.401611+00:00
-- url     : https://prove2.me/theorems/386f33c3-70d3-4a74-b7d1-816d0dc70013
-- title:
--   Lemma 3.5 — positive definite splitting along the RIP
-- statement:
--   Let nonempty blocks $I_l$ satisfy the running intersection property, and let a positive definite rational form of degree $2d$ be written $f=\sum_l f_l$, where each $f_l$ is a continuous rational form in its own block. For each later block, a correction $\varphi_l=q_l/\|x(\widehat I_l)\|_2^{2k_l}$ can be chosen on its overlap so that
--
--   $$h_l=f_l+\varphi_l-\sum_{j>l:s_j=l}\varphi_j,\qquad f=\sum_l h_l,$$
--
--   and every $h_l$ is a continuous rational form positive definite on its own block. Here $\varphi_1=0$. **Formalization Note** The Lean statement adds $d>0$: the printed lemma omits it, although its cited continuity and splitting lemmas assume it.
-- source:
--   Mai, Magron & Lasserre, A sparse version of Reznick’s Positivstellensatz, arXiv:2002.05101v2, p. 11, Lemma 3.5

import Mathlib
import Definitions.Def_SparseReznick_Psatz_Model

namespace SparseReznick.Psatz

theorem lemma_3_5 {n p : ℕ} (I : Fin p → Finset (Fin n))
    (s : Fin p → Fin p) (hrip : RIP I s)
    (d : ℕ) (hd : 0 < d) (fl : Fin p → (Fin n → ℝ) → ℝ)
    (hfl : ∀ l, IsContRatForm (I l) (2 * d) (fl l))
    (hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < ∑ l, fl l x) :
    ∃ (k : Fin p → ℕ) (q : Fin p → MvPolynomial (Fin n) ℝ),
      (∀ l, l.val ≠ 0 →
        q l ∈ MvPolynomial.supported ℝ (↑(Ihat I l) : Set (Fin n)) ∧
        (q l).IsHomogeneous (2 * (d + k l))) ∧
      let phi : Fin p → (Fin n → ℝ) → ℝ :=
        fun l => if l.val = 0 then 0 else ratForm (Ihat I l) (q l) (k l)
      let h : Fin p → (Fin n → ℝ) → ℝ :=
        fun l => fl l + phi l -
          ∑ j ∈ Finset.univ.filter (fun j : Fin p => l < j ∧ s j = l), phi j
      (∀ l, IsContRatForm (I l) (2 * d) (h l) ∧ IsPDOn (I l) (h l)) ∧
        ∀ x, (∑ l, fl l x) = ∑ l, h l x := by sorry

end SparseReznick.Psatz
