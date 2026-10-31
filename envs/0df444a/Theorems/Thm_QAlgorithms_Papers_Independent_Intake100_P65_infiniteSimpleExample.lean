-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P65_infiniteSimpleExample
-- name    : QAlgorithms.Papers.Independent.Intake100.P65.infiniteSimpleExample
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:16:27.953964+00:00
-- url     : https://prove2.me/theorems/c2ae5540-d68a-407c-acda-a01e99fa0290
-- title:
--   An explicit infinite-dimensional simple affine module
-- statement:
--   Let $R$ be a field with $2$ invertible and let $\Omega$ be admissible with nonrational generating series $\sum_{j\ge0}\omega_jy^{-j}$. On $V=\bigoplus_{j\ge0}Rv_j$ there exists an irreducible $W_2^{\mathrm{aff}}(\Omega)$-action determined by
--
--   $$Ev_j=\omega_jv_0,\quad X_1v_j=v_{j+1},\quad X_2v_j=-v_{j+1},\quad Sv_j=(-1)^jv_j-\varepsilon_jv_{j-1}+\sum_{k=0}^{j-1}(-1)^k\omega_{j-k-1}v_k.$$
--
--   Here $\varepsilon_j=1$ for odd $j$ and $0$ otherwise, and the term with $v_{j-1}$ is zero at $j=0$. The vector space $V$ is infinite dimensional. This gives the source's explicit infinite-dimensional simple affine module.
-- source:
--   Cyclotomic Nazarov-Wenzl algebras, arXiv:math/0506467v5, PDF p. 10, Example 2.17

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

/-- Example 2.17, PDF p.10. The proof requires a field, omitted in its printed
sentence. The action is constructed on the direct sum with the four specified
operator formulas, and is irreducible and infinite dimensional. -/
theorem infiniteSimpleExample (R : Type u) [Field R] [Invertible (2 : R)]
    (omega : ℕ → R) (ha : OmegaAdmissible omega) (hirr : ¬ RationalSequence omega) :
    ∃ rho : AffineBMW R omega 2 →ₐ[R] Module.End R (ℕ →₀ R),
      IrreducibleRepresentation rho ∧ ¬ FiniteDimensional R (ℕ →₀ R) ∧
      ∀ j : ℕ,
        rho (affineE R omega 2 0) (Finsupp.single j 1) =
          omega j • Finsupp.single 0 1 ∧
        rho (affineX R omega 2 0) (Finsupp.single j 1) = Finsupp.single (j+1) 1 ∧
        rho (affineX R omega 2 1) (Finsupp.single j 1) = -Finsupp.single (j+1) 1 ∧
        rho (affineS R omega 2 0) (Finsupp.single j 1) =
          (-1 : R)^j • Finsupp.single j 1 -
            (if Odd j then Finsupp.single (j-1) 1 else 0) +
            ∑ k ∈ Finset.range j,
              ((-1 : R)^k * omega (j-k-1)) • Finsupp.single k 1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P65

end
