-- Prove2me | Theorems.Thm_SparseReznick_Psatz_theorem_2_1
-- name    : SparseReznick.Psatz.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:46.506231+00:00
-- url     : https://prove2.me/theorems/f91718dc-b320-4e0a-8c5a-2dc399bcd83f
-- title:
--   Theorem 2.1 — sparse rational-form certificate
-- statement:
--   Under the running intersection property, suppose a positive definite rational form of degree $2d$ is $f=\sum_l p_l/\|x(I_l)\|_2^{2k_l}$, where $d>0$ and each $p_l$ is a form of degree $2(d+k_l)$ in its own block. There are a common exponent $k$ and block-supported sums of squares $\sigma_l$ such that
--
--   $$f=\sum_l\frac{\sigma_l}{\|x(I_l)\|_2^{2k}\Phi_l^k},\qquad\sigma_l\in\Sigma[x(I_l)]_{d+k(1+\deg(\Phi_l)/2)}.$$
--
--   This is the paper’s rational-form generalization of the goal. **Formalization Note** Later overlaps are assumed nonempty so the printed denominator is nonzero; the identity is evaluated where all denominators are nonzero.
-- source:
--   Mai, Magron & Lasserre, A sparse version of Reznick’s Positivstellensatz, arXiv:2002.05101v2, p. 6, Theorem 2.1

import Mathlib
import Definitions.Def_SparseReznick_Psatz_Model

namespace SparseReznick.Psatz

theorem theorem_2_1 {n p : ℕ} (I : Fin p → Finset (Fin n))
    (s : Fin p → Fin p) (hrip : RIP I s)
    (hhat : ∀ l, l.val ≠ 0 → (Ihat I l).Nonempty)
    (d : ℕ) (hd : 0 < d) (kl : Fin p → ℕ)
    (pl : Fin p → MvPolynomial (Fin n) ℝ)
    (hpl : ∀ l, pl l ∈ MvPolynomial.supported ℝ (↑(I l) : Set (Fin n)) ∧
      (pl l).IsHomogeneous (2 * (d + kl l)))
    (hpos : ∀ x : Fin n → ℝ, x ≠ 0 →
      0 < ∑ l, ratForm (I l) (pl l) (kl l) x) :
    ∃ (k : ℕ) (sig : Fin p → MvPolynomial (Fin n) ℝ),
      (∀ l, IsSOSIn (I l) (d + k * (1 + degPhi I s l / 2)) (sig l)) ∧
      ∀ x : Fin n → ℝ, (∀ l, MvPolynomial.eval x (H I s l) ≠ 0) →
        (∑ l, ratForm (I l) (pl l) (kl l) x) =
          ∑ l, MvPolynomial.eval x (sig l) /
            (MvPolynomial.eval x (sqNorm (I l)) ^ k *
              MvPolynomial.eval x (Phi I s l) ^ k) := by sorry

end SparseReznick.Psatz
