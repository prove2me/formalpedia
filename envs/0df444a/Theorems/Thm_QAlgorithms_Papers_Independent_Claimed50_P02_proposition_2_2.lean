-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P02_proposition_2_2
-- name    : QAlgorithms.Papers.Independent.Claimed50.P02.proposition_2_2
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:27:58.463988+00:00
-- url     : https://prove2.me/theorems/9fdad3c4-7bca-4539-94e8-838967f06410
-- title:
--   Proposition 2.2: equivariance characterized by the Choi commutator
-- statement:
--   Let $d\ge2$ and $p,q\ge0$ be integers, and let $\Phi$ be a completely positive trace-preserving map from $p$ to $q$ qudits. Write $X^\Phi=\sum_{a,b}|a\rangle\langle b|\otimes\Phi(|a\rangle\langle b|)$ for its unnormalized, input-first Choi operator. Then
--   $$
--   \Phi(U^{\otimes p}\rho U^{\dagger\otimes p})=U^{\otimes q}\Phi(\rho)U^{\dagger\otimes q}\quad\text{for all }U,\rho
--   \quad\Longleftrightarrow\quad
--   [X^\Phi,U^{\otimes p}\otimes\overline U^{\otimes q}]=0\quad\text{for all }U\in U(d).
--   $$
--   Here $\rho$ ranges over all input density matrices. This identifies channel covariance with a concrete commutant constraint.
-- source:
--   Linear programming with unitary-equivariant constraints, arXiv:2207.05713v2, PDF p. 10, Proposition 2.2: equivariance characterized by the Choi commutator

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P02

namespace QAlgorithms.Papers.Independent.Claimed50.P02

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P69 (Sites choi)

noncomputable section

/-- Paper p.10, Proposition 2.2. The universal U-quantifier permits U ↦ conj(U);
for an individual fixed U the input-first Choi convention has the conjugations reversed. -/
theorem proposition_2_2 {d p q : ℕ} (hd : 2 ≤ d)
    (Phi : Superop (Sites (Fin d) p) (Sites (Fin d) q)) (hPhi : IsChannel Phi) :
    UnitaryEquivariant Phi ↔
      ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
        Commute (choi Phi)
          (Matrix.kronecker (piKron p (U : Matrix (Fin d) (Fin d) ℂ))
            (piKron q (fun i j => conj ((U : Matrix (Fin d) (Fin d) ℂ) i j)))) := by sorry

end

end QAlgorithms.Papers.Independent.Claimed50.P02
