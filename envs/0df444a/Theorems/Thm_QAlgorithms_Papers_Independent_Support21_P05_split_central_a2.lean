-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P05_split_central_a2
-- name    : QAlgorithms.Papers.Independent.Support21.P05.split_central_a2
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:35:25.654523+00:00
-- url     : https://prove2.me/theorems/d6cc610b-9a78-442e-a8e4-d21531a9bb3f
-- title:
--   The central E6 coefficient algebra splits into commuting A2 factors
-- statement:
--   Let $A=\mathbb C\times\mathbb C$ be the complexified two-dimensional composition algebra in its idempotent coordinates, with base scalars embedded diagonally, $u_1=(-i,i)$, and $\rho^+=(1,0)$, $\rho^-=(0,1)$. Composition conjugation swaps the coordinates. Let $\mathfrak c=\{h\in M_3(A):\operatorname{tr}_A h=0\}$. For $h=(h_{ij}^+,h_{ij}^-)$, write $h_\pm=(h_{ij}^\pm)$. There is a complex-linear bijection
--
--   $$e:\mathfrak c\longrightarrow\mathfrak{sl}_3(\mathbb C)\oplus\mathfrak{sl}_3(\mathbb C),\qquad e(h)=(h_+,h_-).$$
--
--   It preserves commutators componentwise. More explicitly, $h=\rho^+h_++\rho^-h_-$, each summand has its own traceless complex coefficient matrix, and
--
--   $$[\rho^+a,\rho^-b]=0,\qquad [h,k]=\rho^+[h_+,k_+]+\rho^-[h_-,k_-].$$
--
--   Thus the two specified idempotent coefficient subalgebras are copies of complex $\mathfrak a_2$, giving exactly the split central algebra used by the E6 realization. These are sixteen complex parameters in total.
-- source:
--   Exceptional Lie Algebras, SU(3) and Jordan Pairs Part 2: Zorn-type Representations, arXiv:1403.5120v2, PDF p. 19, §6: split central A2 plus A2

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P05

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P05

open QAlgorithms.Papers.Independent.Information100.P44 (matrixUnit)

/-- §6, PDF pp. 19–20: the specified idempotents split the central algebra into
two commuting copies of complex a2, with a complex-linear bracket-preserving bijection. -/
theorem split_central_a2 :
    ∃ e : E6Central ≃ₗ[ℂ] (Sl3 × Sl3),
      (∀ a, (e a).1.val = (fun i j => (a.val i j).1) ∧
        (e a).2.val = (fun i j => (a.val i j).2) ∧
        a.val = splitJoin (e a).1.val 0 + splitJoin 0 (e a).2.val) ∧
      (∀ a b, matrixComm a.val b.val =
        splitJoin (matrixComm (e a).1.val (e b).1.val)
          (matrixComm (e a).2.val (e b).2.val)) ∧
      (∀ a b : Sl3, matrixComm (splitJoin a.val 0) (splitJoin 0 b.val) = 0) := by sorry

end QAlgorithms.Papers.Independent.Support21.P05

end
