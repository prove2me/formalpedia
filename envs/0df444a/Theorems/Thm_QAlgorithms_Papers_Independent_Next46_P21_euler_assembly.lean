-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P21_euler_assembly
-- name    : QAlgorithms.Papers.Independent.Next46.P21.euler_assembly
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T18:39:47.370458+00:00
-- url     : https://prove2.me/theorems/7041cbf3-cb70-4d58-aa73-3ce130fb32e4
-- title:
--   Euler reduction, error accumulation and circuit assembly
-- statement:
--   Every $U\in SU(2)$ admits real Euler angles $\beta,\gamma,\delta$ satisfying
--
--   $$
--   U=R_z(\beta)H R_z(\gamma)H R_z(\delta).
--   $$
--
--   For these angles, every $\varepsilon>0$ and arbitrary unitary matrices $A,B,D$ satisfying $\|A-R_z(\beta)\|_{\mathrm{op}},\|B-R_z(\gamma)\|_{\mathrm{op}},\|D-R_z(\delta)\|_{\mathrm{op}}\le\varepsilon/3$ obey
--
--   $$
--   \|A H B H D-U\|_{\mathrm{op}}\le\varepsilon.
--   $$
--
--   Here $H$ is the Hadamard matrix and $R_z(\theta)=\operatorname{diag}(e^{-i\theta/2},e^{i\theta/2})$. If $a,b,d$ are chronological Clifford+T lists representing $A,B,D$, respectively, their assembled list is $d,H,b,H,a$. Its matrix is $A H B H D$ and its T-count is $T(a)+T(b)+T(d)$. The count denotes actual T instructions; the Clifford H instructions contribute zero. This gives the source's arbitrary-gate reduction without assuming any search terminates.
-- source:
--   Efficient Clifford+T approximation of single-qubit operators, arXiv:1212.6253v2, PDF p. 12, §7.2: arbitrary SU(2) reduction and error accumulation

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P21

open Set

open scoped ComplexConjugate

/-- Section 7.2, PDF p.12: Euler reduction and the epsilon/3 error allocation.
For gate lists the chronological concatenation reverses displayed matrix-product order. -/
theorem euler_assembly :
    (∀ U : Matrix.specialUnitaryGroup Bool ℂ, ∃ beta gamma delta : ℝ,
      (U : Matrix Bool Bool ℂ) = zRotation beta * QAlgorithms.hadamard * zRotation gamma *
        QAlgorithms.hadamard * zRotation delta ∧
      ∀ eps : ℝ, 0 < eps → ∀ A B D : Matrix.unitaryGroup Bool ℂ,
        QAlgorithms.specNorm ((A : Matrix Bool Bool ℂ) - zRotation beta) ≤ eps / 3 →
        QAlgorithms.specNorm ((B : Matrix Bool Bool ℂ) - zRotation gamma) ≤ eps / 3 →
        QAlgorithms.specNorm ((D : Matrix Bool Bool ℂ) - zRotation delta) ≤ eps / 3 →
        QAlgorithms.specNorm ((A : Matrix Bool Bool ℂ) * QAlgorithms.hadamard *
          (B : Matrix Bool Bool ℂ) * QAlgorithms.hadamard * (D : Matrix Bool Bool ℂ) -
          (U : Matrix Bool Bool ℂ)) ≤ eps) ∧
    (∀ a b d : List Letter,
      wordMatrix (assemble a b d) = wordMatrix a * QAlgorithms.hadamard * wordMatrix b *
        QAlgorithms.hadamard * wordMatrix d ∧
      tCount (assemble a b d) = tCount a + tCount b + tCount d) := by sorry

end QAlgorithms.Papers.Independent.Next46.P21

end
