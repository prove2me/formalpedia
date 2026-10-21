-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_example5
-- name    : QAlgorithms.Papers.Independent.Next46.P22.example5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:36:41.318215+00:00
-- url     : https://prove2.me/theorems/c4c4de29-d42b-47d7-9001-7ec7e98d1261
-- title:
--   Example 5
-- statement:
--   Let $L$ be a Lie algebra over any field $F$ and let $\iota:L\to U(L)$ denote the canonical map to its universal enveloping algebra. There exists the Hopf structure on the given $F$-algebra $U(L)$ with primitive generators:
--
--   $$\Delta(\iota v)=\iota v\otimes1+1\otimes\iota v,\qquad \varepsilon(\iota v)=0,\qquad \mathcal S(\iota v)=-\iota v.$$
--
--   If additionally $L\ne0$ and $F$ has characteristic zero, every left integral $t:U(L)\to F$ is zero. There is no finite-dimensionality hypothesis. The nonzero condition matters: $U(0)=F$ has a normalized integral.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 3, Example 5

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

/-- Example 5, PDF pp.3–4: primitive-generator Hopf structure over any F;
all left integrals vanish when L is nonzero and F has characteristic zero. -/
theorem example5 :
    ∃ hopf : HopfAlgebra F (UniversalEnvelopingAlgebra F L),
      hopf.toBialgebra.toAlgebra = (inferInstance : Algebra F (UniversalEnvelopingAlgebra F L)) ∧
      (letI : Algebra F (UniversalEnvelopingAlgebra F L) := hopf.toBialgebra.toAlgebra
       letI : Module F (UniversalEnvelopingAlgebra F L) := Algebra.toModule
       letI : HopfAlgebra F (UniversalEnvelopingAlgebra F L) := hopf
       (∀ v : L,
        Coalgebra.comul (R := F) (UniversalEnvelopingAlgebra.ι F v) =
          UniversalEnvelopingAlgebra.ι F v ⊗ₜ[F] (1 : UniversalEnvelopingAlgebra F L) +
          (1 : UniversalEnvelopingAlgebra F L) ⊗ₜ[F] UniversalEnvelopingAlgebra.ι F v ∧
        Coalgebra.counit (R := F) (UniversalEnvelopingAlgebra.ι F v) = 0 ∧
        HopfAlgebra.antipode F (UniversalEnvelopingAlgebra.ι F v) =
          -UniversalEnvelopingAlgebra.ι F v) ∧
       (Nontrivial L → CharZero F → ∀ t : UniversalEnvelopingAlgebra F L →ₗ[F] F,
        LeftIntegral t → t = 0)) := by sorry

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
