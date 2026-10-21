-- Prove2me | Theorems.Thm_SparseReznick_Psatz_lemma_3_2
-- name    : SparseReznick.Psatz.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:48.409597+00:00
-- url     : https://prove2.me/theorems/22571890-4836-4456-a157-802db95f563f
-- title:
--   Lemma 3.2 — continuity of a rational homogeneous form
-- statement:
--   For $n>0$, let $d>0$, $k\in\mathbb N$, and let $q$ be a homogeneous real form of degree $2(d+k)$. Define $g(x)=q(x)/\|x\|_2^{2k}$, with value zero at the origin when the denominator is zero. Then
--
--   $$g\text{ is continuous},\qquad g(tx)=t^{2d}g(x)\quad(t\in\mathbb R).$$
--
--   The result supplies the continuity and degree needed for the rational corrections in the later block-splitting lemmas.
-- source:
--   Mai, Magron & Lasserre, A sparse version of Reznick’s Positivstellensatz, arXiv:2002.05101v2, p. 9, Lemma 3.2

import Mathlib
import Definitions.Def_SparseReznick_Psatz_Model

namespace SparseReznick.Psatz

theorem lemma_3_2 {n : ℕ} (hn : 0 < n) (d k : ℕ) (hd : 0 < d)
    (q : MvPolynomial (Fin n) ℝ) (hq : q.IsHomogeneous (2 * (d + k))) :
    Continuous (ratForm Finset.univ q k) ∧
      ∀ (t : ℝ) (x : Fin n → ℝ),
        ratForm Finset.univ q k (t • x) =
          t ^ (2 * d) * ratForm Finset.univ q k x := by sorry

end SparseReznick.Psatz
