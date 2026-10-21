-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_remark4_3
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.remark4_3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:37:42.472635+00:00
-- url     : https://prove2.me/theorems/300f60b1-19ef-4971-9748-c5cb3cc8c0c2
-- title:
--   Diagonal contraction variant
-- statement:
--   Let $R,S$ be nonzero finite-dimensional complex Hilbert spaces, $n\ge1$, $\rho\ge0$ a permutation-invariant operator on $R^{\otimes n}\otimes S^{\otimes n}$, and $\sigma\ge0$ on $R\otimes S$. Let $W$ be a permutation-invariant contraction on $R^{\otimes n}$. Fix an orthonormal basis of $R$ and suppose $W$ is diagonal in its $n$-fold product basis. With $d=(\dim R)^2(\dim S)^2$, there exists an operator $U$ diagonal in that single-copy basis with $\|U\|_\infty\le1$ satisfying
--
--   $$F\bigl(\rho,U^{\otimes n}\sigma^{\otimes n}(U^{\otimes n})^\dagger\bigr)\ge(n+1)^{-d^2}F\bigl(W\rho W^\dagger,\sigma^{\otimes n}\bigr).$$
--
--   Here $\rho,\sigma$ are nonnegative, $\rho$ and $W$ are permutation invariant, and $F$ is root fidelity with identities on $S$. This variant preserves a preferred diagonal basis.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 14, Remark 4.3

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Remark 4.3 (PDF p.14): diagonal contraction U in the specified ON basis,
with d=(dim R)^2(dim S)^2, and the Eq.88 exponent -d². -/
theorem remark4_3 {R S : Type*} [Fintype R] [Fintype S]
    [DecidableEq R] [DecidableEq S] [Nonempty R] [Nonempty S]
    (n : ℕ) (hn : 0 < n)
    (rho : Op ((Fin n → R) × (Fin n → S))) (sigma : Op (R × S))
    (hrho : rho.PosSemidef) (hinv : GroupInvariant rho) (hsigma : sigma.PosSemidef)
    (W : Op (Fin n → R)) (hW : copyPermutationInvariant W) (hc : Contractive W)
    (basis : Matrix.unitaryGroup R ℂ)
    (hdiag : DiagonalIn (matrixPower (basis : Op R) n) W) :
    ∃ U : Op R, Contractive U ∧ DiagonalIn (basis : Op R) U ∧
      fidelityFactor n (Fintype.card R ^ 2 * Fintype.card S ^ 2) *
        rootFidelity (liftFirst W * rho * (liftFirst W)ᴴ) (groupedPower sigma n) ≤
      rootFidelity rho (liftFirst (matrixPower U n) * groupedPower sigma n *
        (liftFirst (matrixPower U n))ᴴ) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
