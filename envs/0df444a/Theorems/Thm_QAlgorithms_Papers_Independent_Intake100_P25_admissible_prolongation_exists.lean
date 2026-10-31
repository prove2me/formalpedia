-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P25_admissible_prolongation_exists
-- name    : QAlgorithms.Papers.Independent.Intake100.P25.admissible_prolongation_exists
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:23:10.27976+00:00
-- url     : https://prove2.me/theorems/fb3890af-66ca-4e55-ab4c-b34975e74ee2
-- title:
--   §6, explicit construction: existence of an admissible prolongation
-- statement:
--   Let $n\ge1$ and let $\psi:[0,1]\to\operatorname{Sp}(2n,\Omega_0)$ be any continuous path. There exist symplectic endpoint splittings $\psi(i)=\psi^\star(i)\diamond\psi^{(1)}(i)$, where the second summand is the generalized $1$-eigenspace, and a continuous symplectic prolongation $\Psi:[-1,2]\to\operatorname{Sp}(2n,\Omega_0)$ with
--
--   $$\Psi|_{[0,1]}=\psi,\qquad\Psi(-1/2)=\psi^\star(0)\diamond H_0,\qquad\Psi(3/2)=\psi^\star(1)\diamond H_1,$$
--
--   where each $H_i=\operatorname{diag}(e^{-1}I,eI)$ has the dimension of the respective $1$-block. On $[-1/2,0]$ and $[1,3/2]$, each star block is fixed and the other block has only positive real eigenvalues. The endpoints $\Psi(-1)$ and $\Psi(2)$ are independently $W^+$ or $W^-$, and $\Psi$ avoids eigenvalue $1$ on the two outer intervals. Empty endpoint blocks are allowed. This is the existence supplied by the section 6 construction, with no initial-identity, terminal-nondegeneracy or crossing-regularity condition.
-- source:
--   Generalized Conley-Zehnder index, arXiv:1307.7239v1, PDF p. 23, §6, explicit construction

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P25

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Intake100.P25

open QAlgorithms.Papers.Independent.Gap50repair.P01

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

attribute [local instance] Classical.propDecidable

/-- Section 6 construction, PDF pp.22-23: actual existence, for arbitrary endpoints.
The proof's psi_I must conjugate the fixed endpoint p(1), and its comparison
from psi_I(1) includes psi_II before psi_III and psi_IV. These printed proof
endpoint mismatches do not alter the four prolongation clauses. -/
theorem admissible_prolongation_exists {n : ℕ} (hn : 1 ≤ n)
    (p : ℝ → GroupedRealMatrix n) (hp : IsPath p 1) :
    ∃ D0 : EndpointSplitting (p 0), ∃ D1 : EndpointSplitting (p 1),
      ∃ e : ℝ → GroupedRealMatrix n, IsProlongation p e D0 D1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P25

end
