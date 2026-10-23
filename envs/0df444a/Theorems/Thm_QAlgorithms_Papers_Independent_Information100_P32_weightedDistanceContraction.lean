-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P32_weightedDistanceContraction
-- name    : QAlgorithms.Papers.Independent.Information100.P32.weightedDistanceContraction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:48:41.421818+00:00
-- url     : https://prove2.me/theorems/6127ea6e-fe88-4e6b-829d-e59e7fc74837
-- title:
--   Exact weighted norm and trace-distance contraction
-- statement:
--   Let $J,\omega\in\mathbb R$ and $\tau>0$. Each fresh, independent ancillary qubit has the same state $\rho_A=\left(\begin{smallmatrix}p_A&c_A\\c_A^*&1-p_A\end{smallmatrix}\right)$, where $0\le p_A\le1$ and $|c_A|^2\le p_A(1-p_A)$. The system and incoming ancilla are initially uncorrelated. Put $H_S=H_A=-\omega\sigma_z/2$, $H_0=H_S\otimes I+I\otimes H_A$, and $H_I=J(\sigma_x\otimes\sigma_x+\sigma_y\otimes\sigma_y)$. One collision is $\Phi(\rho)=\operatorname{Tr}_A[e^{-i\tau(H_0+H_I)}(\rho\otimes\rho_A)e^{i\tau(H_0+H_I)}]$, with no additional free interval. Units are $\hbar=k_B=1$ and $|0\rangle$ has $\sigma_z$ eigenvalue $+1$. Let $\sigma$ be any physical fixed point of $\Phi$, and $\rho_0$ any density matrix. Use the exact matrix $M$ of Eq.(B2). For $v=(v_0,v_1,v_2)$ let $\|v\|_G^2=|v_0|^2+(|v_1|^2+|v_2|^2)/2$, and let $\|M\|_G$ be its induced norm. Put $r=\sqrt{1-\sin^2(2J\tau)(1-4|c_A|^2)}$ and $D_{\rm tr}(\rho,\sigma)=\frac12\|\rho-\sigma\|_1$. Then $\|M\|_G=r$, and for every $n\ge0$,
--   $$D_{\rm tr}(\sigma,\Phi^n(\rho_0))=\sqrt{(p_n-p_\sigma)^2+|c_n-c_\sigma|^2}=\|M^n X_0\|_G\le r^nD_{\rm tr}(\sigma,\rho_0),$$
--   where $X_0=(p_0-p_\sigma,c_0-c_\sigma,(c_0-c_\sigma)^*)^T$. Only the fixed-point identity is assumed, not attraction. Rate zero and rate one are both covered.
-- source:
--   Coherence -assisted quantum state preparation and thermal control through repeated interactions, arXiv:2610.10794v1, PDF p. 21, Appendix E Eqs.(E2)–(E5): exact weighted norm and distance contraction

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

/-- PDF pp.20–21, Eqs.(E2)–(E5): exact weighted induced norm and trace-distance
contraction about any physical fixed point. r=0 is allowed and r=1 does not assert convergence. -/
theorem weightedDistanceContraction (m : Model) (s r : Op Bool)
    (hs : IsDensityMatrix s) (hr : IsDensityMatrix r) (hfix : collision m s = s) :
    weightedInducedNorm (affineMatrix m) = contractionRate m ∧
    (∀ n : ℕ,
      traceDistance s (trajectory m r n) =
        Real.sqrt ((population (trajectory m r n) - population s) ^ 2 +
          Complex.normSq (coherence (trajectory m r n) - coherence s)) ∧
      traceDistance s (trajectory m r n) =
        weightedNorm (((affineMatrix m) ^ n).mulVec (coordinates (r - s))) ∧
      traceDistance s (trajectory m r n) ≤ contractionRate m ^ n * traceDistance s r) := by sorry

end QAlgorithms.Papers.Independent.Information100.P32

end
