-- Prove2me | Theorems.Thm_SparseReznick_Psatz_lemma_3_4
-- name    : SparseReznick.Psatz.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:50.591005+00:00
-- url     : https://prove2.me/theorems/cf48e67e-18cf-4c7c-acfc-b73b94fa9062
-- title:
--   Lemma 3.4 — positive definite splitting across two blocks
-- statement:
--   For $n>0$, suppose $I_1\cup I_2$ is the full coordinate set, $d>0$, and $f=f_1+f_2$ is a positive definite rational form of degree $2d$, with each $f_i$ a continuous rational form in its own block. Then some homogeneous polynomial $q$ in the overlap and $k\in\mathbb N$ give a continuous rational correction $\varphi=q/\|x(I_1\cap I_2)\|_2^{2k}$ such that
--
--   $$f=(f_1-\varphi)+(f_2+\varphi),$$
--
--   and both resulting forms are positive definite on their respective blocks. This is the two-block positivity statement used in the running-intersection result. **Formalization Note** The source’s parenthetical dependence on an undefined $\varepsilon$ is omitted; $k$ is existential in the stated result.
-- source:
--   Mai, Magron & Lasserre, A sparse version of Reznick’s Positivstellensatz, arXiv:2002.05101v2, p. 10, Lemma 3.4

import Mathlib
import Definitions.Def_SparseReznick_Psatz_Model

namespace SparseReznick.Psatz

theorem lemma_3_4 {n : ℕ} (hn : 0 < n) (I1 I2 : Finset (Fin n))
    (hcover : I1 ∪ I2 = Finset.univ) (d : ℕ) (hd : 0 < d)
    (f1 f2 : (Fin n → ℝ) → ℝ)
    (hf1 : IsContRatForm I1 (2 * d) f1)
    (hf2 : IsContRatForm I2 (2 * d) f2)
    (hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < f1 x + f2 x) :
    ∃ (k : ℕ) (q : MvPolynomial (Fin n) ℝ),
      q ∈ MvPolynomial.supported ℝ (↑(I1 ∩ I2) : Set (Fin n)) ∧
      q.IsHomogeneous (2 * (d + k)) ∧
      let phi := ratForm (I1 ∩ I2) q k
      IsContRatForm I1 (2 * d) (f1 - phi) ∧
      IsPDOn I1 (f1 - phi) ∧
      IsContRatForm I2 (2 * d) (f2 + phi) ∧
      IsPDOn I2 (f2 + phi) := by sorry

end SparseReznick.Psatz
