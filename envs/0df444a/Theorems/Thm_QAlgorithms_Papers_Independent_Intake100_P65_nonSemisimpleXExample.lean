-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P65_nonSemisimpleXExample
-- name    : QAlgorithms.Papers.Independent.Intake100.P65.nonSemisimpleXExample
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:17:03.400728+00:00
-- url     : https://prove2.me/theorems/da6a20be-1e44-4c94-9e87-92411998b790
-- title:
--   A nonsemisimple generator on an irreducible rank-two module
-- statement:
--   Let $R$ be an algebraically closed field with $2$ invertible, and let $\Omega$ be admissible with $\omega_0=1$, $\omega_1=0$, and $\omega_{a+2}=\omega_{a+1}/2-\omega_a/16$ for all $a\ge0$. For each of the two root lists $(1/4,1/4)$ and $(1/4,1/4,-1/2)$, the corresponding $W_{r,2}$ has an irreducible representation on $R^2$ with
--
--   $$E=\begin{pmatrix}1&0\\0&0\end{pmatrix},\quad S=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad X_1=\begin{pmatrix}0&1/4\\-1/4&1/2\end{pmatrix},\quad X_2=-X_1.$$
--
--   Moreover $X_1-\tfrac14I\ne0$ and $(X_1-\tfrac14I)^2=0$. Thus a generator need not act semisimply on a simple module.
-- source:
--   Cyclotomic Nazarov-Wenzl algebras, arXiv:math/0506467v5, PDF p. 14, Remark 3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

/-- Remark 3.3, PDF pp.14--15. The explicit recurrence and matrices give an
irreducible module for both stated root lists, with a nonzero square-zero
X_1-1/4. The two ranks are bound together, rather than selecting one case. -/
theorem nonSemisimpleXExample (R : Type u) [Field R] [IsAlgClosed R]
    [Invertible (2 : R)] (omega : ℕ → R)
    (hzero : omega 0 = 1) (hone : omega 1 = 0)
    (hrec : ∀ a, omega (a+2) = (1/2 : R) * omega (a+1) - (1/16 : R) * omega a)
    (ha : OmegaAdmissible omega) :
    ∀ r : ℕ, r = 2 ∨ r = 3 →
      let roots : Fin r → R := fun i => if i.val < 2 then 1/4 else -1/2
      let x : Matrix (Fin 2) (Fin 2) R := !![0, 1/4; -1/4, 1/2]
      ∃ rho : Cyclotomic R omega .degenerate r roots 2 →ₐ[R]
          Module.End R (Fin 2 → R),
        IrreducibleRepresentation rho ∧
        rho (ce R omega .degenerate r roots 2 0) = Matrix.toLin' !![1,0;0,0] ∧
        rho (cg R omega .degenerate r roots 2 0) = Matrix.toLin' !![1,0;0,-1] ∧
        rho (cy R omega .degenerate r roots 2) = Matrix.toLin' x ∧
        rho (toCycl R omega .degenerate r roots 2 (affineX R omega 2 1)) =
          Matrix.toLin' (-x) ∧
        x - (1/4 : R) • (1 : Matrix (Fin 2) (Fin 2) R) ≠ 0 ∧
        (x - (1/4 : R) • (1 : Matrix (Fin 2) (Fin 2) R))^2 = 0 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P65

end
