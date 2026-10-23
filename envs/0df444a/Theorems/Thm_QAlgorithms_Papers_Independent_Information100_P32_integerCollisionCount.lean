-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P32_integerCollisionCount
-- name    : QAlgorithms.Papers.Independent.Information100.P32.integerCollisionCount
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:49:10.946313+00:00
-- url     : https://prove2.me/theorems/42f3e210-5ab5-42b9-86cc-de756eb892cf
-- title:
--   Corrected natural-number collision bound for strict tolerance
-- statement:
--   Let $J,\omega\in\mathbb R$ and $\tau>0$. Each fresh, independent ancillary qubit has the same state $\rho_A=\left(\begin{smallmatrix}p_A&c_A\\c_A^*&1-p_A\end{smallmatrix}\right)$, where $0\le p_A\le1$ and $|c_A|^2\le p_A(1-p_A)$. The system and incoming ancilla are initially uncorrelated. Put $H_S=H_A=-\omega\sigma_z/2$, $H_0=H_S\otimes I+I\otimes H_A$, and $H_I=J(\sigma_x\otimes\sigma_x+\sigma_y\otimes\sigma_y)$. One collision is $\Phi(\rho)=\operatorname{Tr}_A[e^{-i\tau(H_0+H_I)}(\rho\otimes\rho_A)e^{i\tau(H_0+H_I)}]$, with no additional free interval. Units are $\hbar=k_B=1$ and $|0\rangle$ has $\sigma_z$ eigenvalue $+1$. Let $\sigma$ be a physical fixed point, $\rho_0$ a density matrix, $d_0=D_{\rm tr}(\sigma,\rho_0)$, and $0\le r<1$ the rate in Eq.(E5). Given $\epsilon>0$, define
--   $$B=\begin{cases}0&d_0<\epsilon,\\1&d_0\ge\epsilon,\ r=0,\\\left\lfloor\dfrac{\log\epsilon-\log d_0}{\log r}\right\rfloor+1&d_0\ge\epsilon,\ 0<r<1.\end{cases}$$
--   Every integer $k\ge B$ satisfies $D_{\rm tr}(\sigma,\Phi^k(\rho_0))<\epsilon$. Moreover a first such collision count $n_*\le B$ exists, and every earlier distance is at least $\epsilon$. This explicitly corrects the printed unrounded real bound and handles zero initial distance and equality with the tolerance.
-- source:
--   Coherence -assisted quantum state preparation and thermal control through repeated interactions, arXiv:2610.10794v1, PDF p. 20, Appendix E Eqs.(E6)–(E8): corrected integer collision-count bound

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

/-- Corrected PDF pp.20–21, Eqs.(E6)–(E8): an integer upper bound with strict
tolerance, zero initial distance, initially equal tolerance, and zero rate handled explicitly.
The printed unrounded real upper bound is false and is separately deferred. -/
theorem integerCollisionCount (m : Model) (s r : Op Bool)
    (hs : IsDensityMatrix s) (hr : IsDensityMatrix r) (hfix : collision m s = s)
    (hRate : contractionRate m < 1) (epsilon : ℝ) (he : 0 < epsilon) :
    (∀ k : ℕ, collisionBound (contractionRate m) (traceDistance s r) epsilon ≤ k →
      traceDistance s (trajectory m r k) < epsilon) ∧
    (∃ n : ℕ, n ≤ collisionBound (contractionRate m) (traceDistance s r) epsilon ∧
      traceDistance s (trajectory m r n) < epsilon ∧
      ∀ k : ℕ, k < n → epsilon ≤ traceDistance s (trajectory m r k)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P32

end
