-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P03_discrete_log_reduction
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P03.discrete_log_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:50:42.944342+00:00
-- url     : https://prove2.me/theorems/5d54e251-87ac-4247-97d0-33ea06530e66
-- title:
--   §1 example 2: discrete logarithm from a rank-two stabilizer
-- statement:
--   Let $q$ be prime, let $\zeta$ generate the unit group modulo $q$, and let $g$ be a unit. Suppose an integer basis $B$ is supplied for
--
--   $$
--   P=\{(u,v)\in\mathbb Z^2:\zeta^u g^v=1\}.
--   $$
--
--   One classical procedure, polynomial in the binary input length and chosen before $q,\zeta,g,B$, returns an integer $m$ such that
--
--   $$
--   0\le m<q-1,\qquad (m,-1)\in P,\qquad \zeta^m=g.
--   $$
--
--   For $q=2$, the representative is necessarily zero. This identifies the exact information extracted from a stabilizer basis.
-- source:
--   Quantum measurements and the Abelian Stabilizer Problem, arXiv:quant-ph/9511026v1, PDF p. 4, §1 example 2: discrete logarithm from a rank-two stabilizer

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P03

noncomputable section

open scoped Matrix ComplexConjugate Kronecker

namespace QAlgorithms.Papers.Independent.Intakethird100.P03

open QAlgorithms.Papers.Independent.Renew46.P01 (cleanVector)

attribute [local instance] Classical.propDecidable

/-- PDF p.4, example 2: one classical polynomial-time procedure extracts m modulo q-1
from a basis of P, with (m,-1) in P and zeta^m=g. q=2 returns the representative zero. -/
theorem discrete_log_reduction :
    ∃ extract : List Bool → List Bool, QAlgorithms.Complexity.PolyTimeComputable extract ∧
      ∀ (q : ℕ), Nat.Prime q → ∀ (zeta g : (ZMod q)ˣ), orderOf zeta = q - 1 →
      ∀ B : Matrix (Fin 2) (Fin 2) ℤ, IsLatticeBasis B →
      (∀ v : Fin 2 → ℤ, v ∈ columnLattice B ↔ zeta ^ (v 0) * g ^ (v 1) = 1) →
      ∃ m : ℕ, m < q - 1 ∧
        extract (discreteLogInput q zeta g B) = encodeNatural m ∧
        (![((m : ℕ) : ℤ), -1] : Fin 2 → ℤ) ∈ columnLattice B ∧ zeta ^ m = g := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P03

end
