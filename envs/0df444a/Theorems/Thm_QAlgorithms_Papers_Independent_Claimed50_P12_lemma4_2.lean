-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_lemma4_2
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.lemma4_2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:36:45.768667+00:00
-- url     : https://prove2.me/theorems/dc0b1b2d-3d7a-42dd-a232-0c3678fd214f
-- title:
--   Replace an invariant contraction by a single-copy unitary
-- statement:
--   Let $R,S$ be nonzero finite-dimensional complex Hilbert spaces, $n\ge1$, $\rho\ge0$ a permutation-invariant operator on $R^{\otimes n}\otimes S^{\otimes n}$, and $\sigma\ge0$ on $R\otimes S$. Let $W$ be permutation invariant on $R^{\otimes n}$ with $\|W\|_\infty\le1$, and put $d=(\dim R)(\dim S)^2$. There is a unitary $U$ on $R$ such that
--
--   $$F\bigl(\rho,U^{\otimes n}\sigma^{\otimes n}(U^{\otimes n})^\dagger\bigr)\ge(n+1)^{-d^2}F\bigl(W\rho W^\dagger,\sigma^{\otimes n}\bigr).$$
--
--   Identities on $S$ are understood; $F$ is root fidelity. The contraction need not be positive, and $U$ may depend on all the displayed data. The result replaces a collective filter by a local rotation.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 13, Lemma 4.2

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

/-- Lemma 4.2 (PDF p.13, Eq.88): arbitrary invariant contraction W; local U may depend
on n, rho, sigma and W. All identities on S are explicit. -/
theorem lemma4_2 {R S : Type*} [Fintype R] [Fintype S]
    [DecidableEq R] [DecidableEq S] [Nonempty R] [Nonempty S]
    (n : ℕ) (hn : 0 < n)
    (rho : Op ((Fin n → R) × (Fin n → S))) (sigma : Op (R × S))
    (hrho : rho.PosSemidef) (hinv : GroupInvariant rho) (hsigma : sigma.PosSemidef)
    (W : Op (Fin n → R)) (hW : copyPermutationInvariant W) (hc : Contractive W) :
    ∃ U : Matrix.unitaryGroup R ℂ,
      fidelityFactor n (dimensionParameter R S) *
        rootFidelity (liftFirst W * rho * (liftFirst W)ᴴ) (groupedPower sigma n) ≤
      rootFidelity rho (liftFirst (matrixPower (U : Op R) n) * groupedPower sigma n *
        (liftFirst (matrixPower (U : Op R) n))ᴴ) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
