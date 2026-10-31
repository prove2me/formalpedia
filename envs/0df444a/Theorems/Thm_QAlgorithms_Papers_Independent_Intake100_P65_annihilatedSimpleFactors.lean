-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P65_annihilatedSimpleFactors
-- name    : QAlgorithms.Papers.Independent.Intake100.P65.annihilatedSimpleFactors
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:15:56.503425+00:00
-- url     : https://prove2.me/theorems/d2ca6ee3-2af9-4284-8920-2cc33a009fce
-- title:
--   A contraction-annihilated simple action factors through Hecke
-- statement:
--   Let $R$ be a field with $2$ invertible, $n\ge2$, $r\ge1$, $u\in R^r$, and $\Omega$ admissible. Let $M$ be a nonzero irreducible $W_{r,n}(u;\Omega)$-module with specified action $\rho$, annihilated by some $E_i$ with $1\le i<n$. There is the generator-compatible surjective quotient map $q:W_{r,n}\to H_{r,n}(u)$, sending $S_i\mapsto T_i$, $E_i\mapsto0$, and $X_j\mapsto Y_j$, and an irreducible action $\sigma$ on the same vector space satisfying
--
--   $$\sigma\circ q=\rho.$$
--
--   Thus the existing module descends, rather than being replaced by an unrelated Hecke module.
-- source:
--   Cyclotomic Nazarov-Wenzl algebras, arXiv:math/0506467v5, PDF p. 10, Corollary 2.16

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

/-- Corollary 2.16, PDF p.10. The existing irreducible W-action factors
through the canonical, generator-compatible, surjective Hecke quotient.
No finite-dimensionality premise is imposed on M. -/
theorem annihilatedSimpleFactors (R : Type u) [Field R] [Invertible (2 : R)]
    (omega : ℕ → R) (n r : ℕ) (hn : 2 ≤ n) (hr : 1 ≤ r)
    (roots : Fin r → R) (ha : OmegaAdmissible omega)
    (V : Type u) [AddCommGroup V] [Module R V]
    (rho : Cyclotomic R omega .degenerate r roots n →ₐ[R] Module.End R V)
    (hirr : IrreducibleRepresentation rho)
    (he : ∃ i : ℕ, i+1 < n ∧ rho (ce R omega .degenerate r roots n i) = 0) :
    ∃ q : Cyclotomic R omega .degenerate r roots n →ₐ[R] CyclotomicHeckeAlgebra R n r roots,
      Function.Surjective q ∧
      (∀ i, i+1<n → q (cg R omega .degenerate r roots n i) = hT R n r roots i ∧
        q (ce R omega .degenerate r roots n i) = 0) ∧
      (∀ j, j<n → q (affineCyclotomicProjection R omega n r roots (by omega) (affineX R omega n j)) =
        hY R n r roots j) ∧
      ∃ sigma : CyclotomicHeckeAlgebra R n r roots →ₐ[R] Module.End R V,
        sigma.comp q = rho ∧ IrreducibleRepresentation sigma := by sorry

end QAlgorithms.Papers.Independent.Intake100.P65

end
