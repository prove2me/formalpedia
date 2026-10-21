-- Prove2me | Theorems.Thm_SparseReznick_Psatz_corollary_2_1
-- name    : SparseReznick.Psatz.corollary_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:51.875467+00:00
-- url     : https://prove2.me/theorems/183c4478-2546-4a1e-a40e-68cf32d82df6
-- title:
--   Corollary 2.1 — sparse Reznick Positivstellensatz
-- statement:
--   Suppose nonempty blocks $I_l$ cover the coordinates and satisfy the running intersection property. Let $d>0$ and let $f=\sum_l f_l$ be a positive definite form of degree $2d$, with each homogeneous $f_l$ supported on its block $I_l$. Then a common $k\in\mathbb N$ and sums of squares $\sigma_l$ in those same blocks satisfy
--
--   $$f=\sum_l\frac{\sigma_l}{H_l^k},\qquad H_l=\|x(I_l)\|_2^2\Phi_l,\qquad\sigma_l\in\Sigma[x(I_l)]_{d+k(1+\deg(\Phi_l)/2)}.$$
--
--   This is the sparse polynomial certificate stated in the paper’s abstract. Individual $f_l$ need not be nonnegative. **Formalization Note** Every later overlap is assumed nonempty so each printed $H_l$ is a nonzero polynomial. The identity is stated at points where all denominators are nonzero.
-- source:
--   Mai, Magron & Lasserre, A sparse version of Reznick’s Positivstellensatz, arXiv:2002.05101v2, p. 6, Corollary 2.1

import Mathlib
import Definitions.Def_SparseReznick_Psatz_Model

namespace SparseReznick.Psatz

theorem corollary_2_1 {n p : ℕ} (I : Fin p → Finset (Fin n))
    (s : Fin p → Fin p) (hrip : RIP I s)
    (hhat : ∀ l, l.val ≠ 0 → (Ihat I l).Nonempty)
    (d : ℕ) (hd : 0 < d) (f : MvPolynomial (Fin n) ℝ)
    (hf : IsPDForm f (2 * d))
    (fl : Fin p → MvPolynomial (Fin n) ℝ)
    (hfl : ∀ l, fl l ∈ MvPolynomial.supported ℝ (↑(I l) : Set (Fin n)) ∧
      (fl l).IsHomogeneous (2 * d))
    (hdecomp : f = ∑ l, fl l) :
    ∃ (k : ℕ) (sig : Fin p → MvPolynomial (Fin n) ℝ),
      (∀ l, IsSOSIn (I l) (d + k * (1 + degPhi I s l / 2)) (sig l)) ∧
      ∀ x : Fin n → ℝ, (∀ l, MvPolynomial.eval x (H I s l) ≠ 0) →
        MvPolynomial.eval x f =
          ∑ l, MvPolynomial.eval x (sig l) /
            MvPolynomial.eval x (H I s l) ^ k := by sorry

end SparseReznick.Psatz
