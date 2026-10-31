-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P65_heckeSemisimpleCriterion
-- name    : QAlgorithms.Papers.Independent.Intake100.P65.heckeSemisimpleCriterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:23:39.144856+00:00
-- url     : https://prove2.me/theorems/1f7b67e3-2beb-44b9-8b2f-c83ec2cf831c
-- title:
--   Exact semisimplicity criterion for the degenerate Hecke algebra
-- statement:
--   Let $R$ be a field with $2$ invertible, let $n,r\ge1$, and let $u\in R^r$ be arbitrary. For the degenerate cyclotomic Hecke algebra $H=H_{r,n}(u)$ one has
--
--   $$H\text{ semisimple}\ \Longleftrightarrow\ H\text{ split semisimple}\ \Longleftrightarrow\ \bigl(\operatorname{char}R=0\text{ or }\operatorname{char}R>n\bigr)\ \text{and $u$ is Hecke-generic}.$$
--
--   Here Hecke-genericity tests $u_i-u_j=d$ only for distinct component indices. Split semisimplicity is an algebra isomorphism to a finite product of full matrix algebras. This criterion places genericity in the conclusion and involves no $\Omega$ parameter.
-- source:
--   Cyclotomic Nazarov-Wenzl algebras, arXiv:math/0506467v5, PDF p. 43, Theorem 6.11

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

/-- Theorem 6.11, PDF pp.43--44. The tuple is arbitrary: genericity and the
characteristic bound are CONCLUSIONS of the criterion. Split and ordinary
semisimplicity are both included, without any Omega hypothesis.
Printed: char R>n and genericity from Definition 6.4. Changed: include char
zero and compare only distinct components. The real specialization on p.41
and the converse proof on p.44 require exactly these two corrections. -/
theorem heckeSemisimpleCriterion (R : Type u) [Field R] [Invertible (2 : R)]
    (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) (roots : Fin r → R) :
    (IsSemisimpleRing (CyclotomicHeckeAlgebra R n r roots) ↔ SplitMatrixAlgebra R (CyclotomicHeckeAlgebra R n r roots)) ∧
    (SplitMatrixAlgebra R (CyclotomicHeckeAlgebra R n r roots) ↔
      (ringChar R = 0 ∨ n < ringChar R) ∧ HeckeGeneric n roots) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P65

end
