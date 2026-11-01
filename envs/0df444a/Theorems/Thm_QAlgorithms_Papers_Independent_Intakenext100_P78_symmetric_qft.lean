-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P78_symmetric_qft
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P78.symmetric_qft
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:55:47.7767+00:00
-- url     : https://prove2.me/theorems/a7a73f96-1c3b-443f-8949-c60c7d9f6688
-- title:
--   Symmetric groups: a polynomial-size ideal QFT in Young orthogonal coordinates
-- statement:
--   For each $n\ge2$, use the point-stabilizer tower of $S_n$ and its transversal products. Fix the Young orthogonal realization: the row and column labels are standard tableaux of the same shape $\lambda$, and $d_\lambda$ is the number of such tableaux. The input encoding records the chosen transversal digits, and the output encoding records the two tableau paths. There are absolute $C>0$ and $k\in\mathbb N$ such that, for every $n\ge2$, a single circuit of ideal one- and two-qubit unitaries, chosen before the amplitudes, has at most
--
--   $$C\bigl(1+\lceil\log_2(n!)\rceil\bigr)^k$$
--
--   gates and maps every normalized input $\sum_g f(g)|g\rangle$ to the clean encoded Fourier state with amplitudes
--
--   $$\widehat f(\lambda)_{T,U}=\sqrt{\frac{d_\lambda}{n!}}\sum_{g\in S_n}f(g)\rho_\lambda(g)_{T,U}.$$
--
--   Here normalized means $\sum_g|f(g)|^2=1$. Additional wires end in zero, and behavior on invalid binary codes is unconstrained. This gives the paper's polylogarithmic ideal gate bound in the named basis. It asserts neither a numerical synthesis algorithm nor a finite-alphabet approximation guarantee.
-- source:
--   Generic Quantum Fourier Transforms, arXiv:quant-ph/0304064v1, PDF p. 8, Unnumbered application: symmetric groups

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P78

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P78

open QAlgorithms

attribute [local instance] Classical.propDecidable

/-- PDF pp.5,8, unnumbered symmetric-group application: the normalized QFT
in the Young orthogonal basis has polylog(|S_n|) ideal elementary gate size.
The same circuit works for all normalized amplitudes; n=0,1 are absorbed
by the finite small-rank convention, and no synthesis/runtime/error claim
is added. The input is the explicit point-stabilizer transversal product. -/
theorem symmetric_qft :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∃ q : ℕ, 4 * n * Nat.clog 2 (n + 1) ≤ q ∧
        ∃ c : Circuit oneTwoQubitGateSet q,
          (c.size : ℝ) ≤ C * ((1 + Nat.clog 2 n.factorial : ℕ) : ℝ) ^ k ∧
          realizesEncodedTransform c (symmetricInputCode n q) (symmetricOutputCode n q)
            symmetricFourier := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P78

end
