-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_tester_normalization
-- name    : QAlgorithms.Papers.Independent.Dependency50.P26.tester_normalization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:39:47.689909+00:00
-- url     : https://prove2.me/theorems/95412027-8386-419d-a2c6-1b584a130413
-- title:
--   §IV E Eq.(67): tester normalization
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces of positive dimension with fixed orthonormal bases. Let $\{P_i\}$ be an $N$-tester, $N\ge1$, and set $T=\sum_iP_i$. In zero-based wire labels there are positive operators $\Theta_j$ on $H_{2j}\otimes\cdots\otimes H_0$ satisfying
--
--   $$
--   T=I_{H_{2N-1}}\otimes\Theta_{N-1},\qquad\operatorname{Tr}_{H_{2j}}\Theta_j=I_{H_{2j-1}}\otimes\Theta_{j-1}\ (1\le j\le N-1),\qquad\operatorname{Tr}\Theta_0=1.
--   $$
--
--   This is the full recursion obtained from Lemma 8 and Eq.(25), correcting the inconsistent indices printed in Eq.(67).
-- source:
--   Theoretical framework for quantum networks, arXiv:0904.4483v2, PDF p. 17, §IV E Eq.(67): tester normalization

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF p.17, Eq.(67): full tester recursion, reindexed to the actual 2(n+1) wires.
Printed I_(2N+2), mixed n/N, and Tr_1 Θ^0 are corrected through Lemma 8. -/
theorem tester_normalization (s : Signature) (n k : ℕ)
    (P : Fin k → Matrix (Basis s (n+1)) (Basis s (n+1)) ℂ)
    (hP : CombTester s (n+1) k P) :
    ∃ T : Matrix (Fin (s.input n) × Basis s n) _ ℂ,
      ThetaNormalized s n T ∧
        (∑ i, P i) = Matrix.kronecker (1 : Matrix (Fin (s.output n)) _ ℂ) T := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P26

end
