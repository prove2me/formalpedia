-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P23_finiteCAR_multiplicity
-- name    : QAlgorithms.Papers.Independent.Intake100.P23.finiteCAR_multiplicity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:11:57.920504+00:00
-- url     : https://prove2.me/theorems/84f7304a-86b3-4fd7-b4f0-d0b4bec5ae4e
-- title:
--   Finite CAR multiplicity classification
-- statement:
--   Let $H$ be a nonzero complex Hilbert space and $n\ge0$. Every self-adjoint CAR tuple $(G_1,\ldots,G_{2n})$ is unitarily equivalent to the printed Jordan–Wigner tuple $J_1,\ldots,J_{2n}$ with a Hilbert multiplicity space $K$:
--   $$U(J_j\otimes1_K)=G_jU,\qquad U:(\mathbb C^2)^{\otimes n}\otimes K\overset{\sim}{\longrightarrow}H.$$
--   It is irreducible exactly when $K$ is unitarily isomorphic to $\mathbb C$. For every CAR tuple of length $2n+1$ there are Hilbert spaces $K_+,K_-$, possibly zero, and a unitary from $(\mathbb C^2)^{\otimes n}\otimes(K_+\oplus K_-)$ to $H$ such that
--   $$U(J_j\otimes1)=G_jU\ (1\le j\le2n),\qquad U(I_n\otimes(1_{K_+}\oplus-1_{K_-}))=G_{2n+1}U.$$
--   This retains both odd multiplicities and the even irreducibility criterion. **Formalization Note** The bounded operator equalities are tested on all pure tensors, which span a dense subspace of the completed tensor product; this is equivalent to equality of the full bounded operators.
-- source:
--   Introduction to representations of the canonical commutation and anticommutation relations, arXiv:math-ph/0511030v2, PDF p. 17, Theorem 10

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P23

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P23

open QAlgorithms.Papers.Independent.Renew46.P03 (tensorVector)

variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section FiniteMultiplicity

universe u

/-- PDF p.17, Theorem 10: the full even/odd multiplicity classification.
The equations are tested on every pure tensor, a dense spanning set in the
completed tensor product; all maps in these equations are bounded. Thus these
are the complete operator intertwining equalities, not core-only identities.
K_+ and K_- are allowed to be zero. The even scalar condition means unitary
isomorphism to C, the intrinsic interpretation of the source's K=C. -/
theorem finiteCAR_multiplicity
    {H0 : Type u} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]
    [CompleteSpace H0] [Nontrivial H0] (n : ℕ) :
    (∀ G : Fin (2 * n) → H0 →L[ℂ] H0, OperatorCAR G →
      ∃ K : MultiplicityHilbert.{u},
      ∃ U : UniformSpace.Completion
          (TensorProduct ℂ (EuclideanSpace ℂ (Fin n → Bool)) K.carrier) ≃ₗᵢ[ℂ] H0,
        (∀ (j : Fin (2 * n)) (x : EuclideanSpace ℂ (Fin n → Bool)) (v : K.carrier),
          U (tensorVector (Matrix.toEuclideanLin (jordanWignerEven n j) x) v) =
            G j (U (tensorVector x v))) ∧
        (HilbertIrreducible G ↔ Nonempty (K.carrier ≃ₗᵢ[ℂ] ℂ))) ∧
    (∀ G : Fin (2 * n + 1) → H0 →L[ℂ] H0, OperatorCAR G →
      ∃ Kp Km : MultiplicityHilbert.{u},
      ∃ U : UniformSpace.Completion
          (TensorProduct ℂ (EuclideanSpace ℂ (Fin n → Bool))
            (WithLp 2 (Kp.carrier × Km.carrier))) ≃ₗᵢ[ℂ] H0,
        (∀ (j : Fin (2 * n)) (x : EuclideanSpace ℂ (Fin n → Bool))
            (v : WithLp 2 (Kp.carrier × Km.carrier)),
          U (tensorVector (Matrix.toEuclideanLin (jordanWignerEven n j) x) v) =
            G j.castSucc (U (tensorVector x v))) ∧
        (∀ (x : EuclideanSpace ℂ (Fin n → Bool))
            (v : WithLp 2 (Kp.carrier × Km.carrier)),
          U (tensorVector (Matrix.toEuclideanLin (jordanWignerParity n) x)
            (WithLp.toLp 2 (v.ofLp.1, -v.ofLp.2))) =
            G (Fin.last (2 * n)) (U (tensorVector x v)))) := by sorry

end FiniteMultiplicity

end QAlgorithms.Papers.Independent.Intake100.P23

end
