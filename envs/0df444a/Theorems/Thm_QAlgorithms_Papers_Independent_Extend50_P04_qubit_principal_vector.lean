-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P04_qubit_principal_vector
-- name    : QAlgorithms.Papers.Independent.Extend50.P04.qubit_principal_vector
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:13:20.023678+00:00
-- url     : https://prove2.me/theorems/729f7000-068a-4c46-a336-464751f56b37
-- title:
--   §V / Appendix E: explicit normalized qubit principal eigenvector
-- statement:
--   Let $N\ge1$, $t=\lfloor N/2\rfloor+1$, and $0\le l<t$. Put $q=N\pi/(N+2)$ and
--   $$w_l=\begin{cases}(-1)^{N/2-l}\,[\sin(((N+2)/2-l)q)-\sin((N/2-l)q)]/\sin q,&N\text{ even},\\(-1)^{(N-1)/2-l}\sin(((N+1)/2-l)q)/\sin q,&N\text{ odd},\end{cases}\qquad v_l=\frac{w_l}{\sqrt{\sum_j w_j^2}}.$$
--   Let $M$ be one quarter of the tridiagonal matrix with off-diagonal entries one and diagonal entries two, except the first is one and the last is one for even $N$. At $N=1$ its sole entry is $1/4$. Then
--   $$v_l\ge0,\quad\sum_l v_l^2=1,\quad Mv=\lambda_{\max}(M)v.$$
--   This is the explicitly normalized principal eigenvector; the printed scalar convention does not affect its eigenvector.
-- source:
--   Square-root measurements and degradation of the resource state in port-based teleportation scheme, arXiv:2105.14886v4, PDF p. 17, §V / Appendix E: explicit normalized qubit principal eigenvector

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P04

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P04

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

/-- PDF pp.17,25, (87)/(E5): explicit normalized nonnegative principal eigenvector.
The matrix is (E2), with no eigenvalue/channel-fidelity scaling inferred from inconsistent (E1). -/
theorem qubit_principal_vector (N : ℕ) (hN : 1 ≤ N) :
    (∑ l, qubitVector N l ^ 2) = 1 ∧ (∀ l, 0 ≤ qubitVector N l) ∧
    ∃ lambda : ℝ, Matrix.mulVec (qubitMatrix N) (qubitVector N) = lambda • qubitVector N ∧
      ∀ (eta : ℝ) (u : Fin (N / 2 + 1) → ℝ), u ≠ 0 →
        Matrix.mulVec (qubitMatrix N) u = eta • u → eta ≤ lambda := by sorry

end QAlgorithms.Papers.Independent.Extend50.P04

end
