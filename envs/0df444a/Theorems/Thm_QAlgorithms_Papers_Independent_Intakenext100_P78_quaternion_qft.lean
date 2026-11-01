-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P78_quaternion_qft
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P78.quaternion_qft
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:57:00.622572+00:00
-- url     : https://prove2.me/theorems/fbfbc167-af49-4f2e-b800-dbd6bd7b8444
-- title:
--   Generalized quaternion groups: a polylogarithmic ideal QFT for all n
-- statement:
--   For each integer $n\ge2$, let $Q_{4n}=\langle a,\gamma\mid a^{2n}=1,\ \gamma^2=a^n,\ \gamma^{-1}a\gamma=a^{-1}\rangle$, the actual finite group represented by Mathlib's QuaternionGroup. Encode $a^j$ by $j$ and $\gamma a^j$ by $2n+j$, for $0\le j<2n$. Fix the cyclic-subgroup-adapted dual. It contains four one-dimensional characters: $a\mapsto(-1)^e$, with the two choices of square root for $\gamma$ whose square is $(-1)^{ne}$. For each $1\le t<n$, the two-dimensional sector has
--
--   $$\rho_t(a)=\operatorname{diag}(e^{\pi i t/n},e^{-\pi i t/n}),\qquad \rho_t(\gamma)=C_t\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad C_t=\begin{cases}1&t\text{ even},\\ i&t\text{ odd}.\end{cases}$$
--
--   There exist absolute $C>0$ and $k\in\mathbb N$ such that, for every $n\ge2$, one ideal one- and two-qubit circuit of at most
--
--   $$C\bigl(1+\lceil\log_2(4n)\rceil\bigr)^k$$
--
--   gates maps every normalized input to the clean Fourier state with amplitudes $\widehat f(\rho)_{i,j}=\sqrt{d_\rho/(4n)}\sum_{g\in Q_{4n}}f(g)\rho(g)_{i,j}$. The output labels are the four characters and the row/column entries of the $n-1$ two-dimensional sectors, in a fixed binary ordering. This preserves the source's general-$n$ application, beyond the power-of-two case cited there. No precision or measurement probability is asserted.
-- source:
--   Generic Quantum Fourier Transforms, arXiv:quant-ph/0304064v1, PDF p. 10, Unnumbered application: generalized quaternion/dicyclic groups

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P78

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P78

open QAlgorithms

attribute [local instance] Classical.propDecidable

/-- PDF p.10, unnumbered quaternionic application: a polylog(4n)-size ideal
QFT for every finite generalized quaternion/dicyclic group with n>=2,
not just the power-of-two subfamily cited in [21]. Constants precede n,
and the circuit precedes every normalized amplitude function. -/
theorem quaternion_qft :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ n : ℕ, ∀ hn : 2 ≤ n,
      letI : NeZero n := ⟨by omega⟩
      ∃ q : ℕ, Nat.clog 2 (4 * n) ≤ q ∧ ∃ c : Circuit oneTwoQubitGateSet q,
        (c.size : ℝ) ≤ C * ((1 + Nat.clog 2 (4 * n) : ℕ) : ℝ) ^ k ∧
        realizesEncodedTransform c (quaternionInputCode n q) (quaternionOutputCode n q)
          quaternionFourier := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P78

end
