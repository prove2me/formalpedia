-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_example2
-- name    : QAlgorithms.Papers.Independent.Next46.P22.example2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:35:20.229982+00:00
-- url     : https://prove2.me/theorems/0caaec02-574a-4e54-a10f-1ee032f06e39
-- title:
--   Example 2
-- statement:
--   Let $F$ have characteristic zero and let $H$ be a finite-dimensional semisimple Hopf algebra over $F$. Write $\Delta(a)=\sum a_1\otimes a_2$, $\varepsilon$ for its counit and $\mathcal S$ for its antipode. There exists an $F$-linear functional $t:H\to F$ satisfying, for every $a,b\in H$,
--
--   $$\sum t(a_2)a_1=t(a)1,\qquad \sum t(a_1b\mathcal S(a_2))=\varepsilon(a)t(b),\qquad t(1)=1.$$
--
--   Thus $t$ is a normalized ad-invariant left integral. Finite-dimensional semisimplicity and cosemisimplicity are equivalent under these characteristic-zero hypotheses; the integral is produced, not assumed.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 3, Example 2

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

/-- Example 2, PDF p.3: existence of the integral is the conclusion. -/
theorem example2 [CharZero F] [FiniteDimensional F H] [IsSemisimpleRing H] :
    ∃ t : H →ₗ[F] F, NormalizedAdIntegral t := by sorry

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
