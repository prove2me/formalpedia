-- Prove2me | Theorems.Thm_SparseReznick_Psatz_lemma_3_6
-- name    : SparseReznick.Psatz.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:50.493508+00:00
-- url     : https://prove2.me/theorems/68f248b8-58f5-46c1-b78b-29846ea28918
-- title:
--   Lemma 3.6 — one rational SOS denominator
-- statement:
--   For $n>0$, let nonempty variable blocks $I_l$ cover all coordinates, let $d>0$, and suppose the positive definite rational form $f$ has summands $q_l/\|x(I_l)\|_2^{2k_l}$, with $q_l$ supported on $I_l$ and homogeneous of degree $2(d+k_l)$. Then some $k\in\mathbb N$ and sum of squares $\sigma\in\Sigma[x]_{d+k(p+1)}$ satisfy
--
--   $$f=\frac{\sigma}{\|x\|_2^{2k}\prod_l\|x(I_l)\|_2^{2k}}.$$
--
--   The identity holds wherever every denominator is nonzero. **Formalization Note** Nonempty blocks are explicit because an empty block makes a displayed denominator the zero polynomial.
-- source:
--   Mai, Magron & Lasserre, A sparse version of Reznick’s Positivstellensatz, arXiv:2002.05101v2, p. 12, Lemma 3.6

import Mathlib
import Definitions.Def_SparseReznick_Psatz_Model

namespace SparseReznick.Psatz

theorem lemma_3_6 {n p : ℕ} (hn : 0 < n) (I : Fin p → Finset (Fin n))
    (hcover : Finset.univ.biUnion I = Finset.univ)
    (hnonempty : ∀ l, (I l).Nonempty) (d : ℕ) (hd : 0 < d)
    (kl : Fin p → ℕ) (q : Fin p → MvPolynomial (Fin n) ℝ)
    (hq : ∀ l, q l ∈ MvPolynomial.supported ℝ (↑(I l) : Set (Fin n)) ∧
      (q l).IsHomogeneous (2 * (d + kl l)))
    (hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < ∑ l, ratForm (I l) (q l) (kl l) x) :
    ∃ (k : ℕ) (sig : MvPolynomial (Fin n) ℝ),
      IsSOSIn Finset.univ (d + k * (p + 1)) sig ∧
      ∀ x : Fin n → ℝ,
        MvPolynomial.eval x (sqNorm Finset.univ) ≠ 0 →
        (∀ l, MvPolynomial.eval x (sqNorm (I l)) ≠ 0) →
        (∑ l, ratForm (I l) (q l) (kl l) x) =
          MvPolynomial.eval x sig /
            (MvPolynomial.eval x (sqNorm Finset.univ) ^ k *
              ∏ l, MvPolynomial.eval x (sqNorm (I l)) ^ k) := by sorry

end SparseReznick.Psatz
