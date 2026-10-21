-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_example9
-- name    : QAlgorithms.Papers.Independent.Next46.P22.example9
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:38:05.531123+00:00
-- url     : https://prove2.me/theorems/f432f475-840c-4519-82df-b7d61c6e9b94
-- title:
--   Example 9
-- statement:
--   Let $F$ be any field, $\mathfrak g$ and $L$ arbitrary $F$-Lie algebras, and $\delta:\mathfrak g\to\operatorname{Der}_F(L)$ a fixed Lie homomorphism. With its primitive-generator Hopf structure, the universal enveloping algebra has the corresponding algebra representation $\alpha:U(\mathfrak g)\to\operatorname{End}_F(L)$ and
--
--   $$\alpha(\iota a)v=\delta(a)v,\qquad h[v,w]=\sum[h_1v,h_2w].$$
--
--   The Hopf structure has $\Delta(\iota a)=\iota a\otimes1+1\otimes\iota a$, $\varepsilon(\iota a)=0$ and $\mathcal S(\iota a)=-\iota a$. Thus the extension of the given derivation action makes $L$ a module Lie algebra, without a dimension or characteristic restriction.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 5, Example 9

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

/-- Example 9, PDF p.5: extension of the GIVEN derivation action for arbitrary g,L.
The primitive Hopf structure and the uniquely pinned action extension are produced. -/
theorem example9 {K : Type*} [LieRing K] [LieAlgebra F K]
    (delta : K →ₗ⁅F⁆ LieDerivation F L L) :
    ∃ hopf : HopfAlgebra F (UniversalEnvelopingAlgebra F K),
      hopf.toBialgebra.toAlgebra = (inferInstance : Algebra F (UniversalEnvelopingAlgebra F K)) ∧
      (letI : Algebra F (UniversalEnvelopingAlgebra F K) := hopf.toBialgebra.toAlgebra
       letI : Module F (UniversalEnvelopingAlgebra F K) := Algebra.toModule
       letI : HopfAlgebra F (UniversalEnvelopingAlgebra F K) := hopf
       (∀ a : K,
        Coalgebra.comul (R := F) (UniversalEnvelopingAlgebra.ι F a) =
          UniversalEnvelopingAlgebra.ι F a ⊗ₜ[F] (1 : UniversalEnvelopingAlgebra F K) +
          (1 : UniversalEnvelopingAlgebra F K) ⊗ₜ[F] UniversalEnvelopingAlgebra.ι F a ∧
        Coalgebra.counit (R := F) (UniversalEnvelopingAlgebra.ι F a) = 0 ∧
        HopfAlgebra.antipode F (UniversalEnvelopingAlgebra.ι F a) =
          -UniversalEnvelopingAlgebra.ι F a) ∧
       ∃ alpha : UniversalEnvelopingAlgebra F K →ₐ[F] Module.End F L,
        (∀ a v, alpha (UniversalEnvelopingAlgebra.ι F a) v = delta a v) ∧ ModuleLie alpha) := by sorry

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
