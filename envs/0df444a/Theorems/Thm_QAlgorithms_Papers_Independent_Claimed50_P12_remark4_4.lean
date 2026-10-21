-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_remark4_4
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.remark4_4
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:38:33.709988+00:00
-- url     : https://prove2.me/theorems/2de7e24a-eaea-4833-adb0-aa4492e1ff7a
-- title:
--   Product-state finite-copy and asymptotic fidelity bounds
-- statement:
--   Let $R,S$ be nonzero finite-dimensional complex Hilbert spaces and $\rho,\sigma\ge0$ on $R\otimes S$. Set $d=(\dim R)(\dim S)^2$ and let $F$ denote root fidelity. For every $n\ge1$ and every permutation-invariant contraction $W$ on $R^{\otimes n}$, there exists a unitary $U$ on $R$ with
--
--   $$F(\rho,U\sigma U^\dagger)\ge\left[(n+1)^{-d^2}F(W\rho^{\otimes n}W^\dagger,\sigma^{\otimes n})\right]^{1/n}.$$
--
--   For every family of permutation-invariant nonnegative contractions $W_n$ one also has
--
--   $$\sup_{U\ \mathrm{unitary}}F(\rho,U\sigma U^\dagger)\ge\limsup_{n\to\infty}F(W_n\rho^{\otimes n}W_n^\dagger,\sigma^{\otimes n})^{1/n}.$$
--
--   All local operators carry the identity on $S$. The unitary family is nonempty and the fidelity values are bounded by $\sqrt{\operatorname{tr}\rho\operatorname{tr}\sigma}$, so the real supremum and limsup are meaningful. These formulas eliminate polynomial losses asymptotically.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 14, Remark 4.4

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

/-- Remark 4.4 (PDF p.14): both Eq.100 and Eq.101. The nth root encloses the
whole RHS in Eq.100. Eq.101 assumes W_n is nonnegative, as printed. -/
theorem remark4_4 {R S : Type*} [Fintype R] [Fintype S]
    [DecidableEq R] [DecidableEq S] [Nonempty R] [Nonempty S]
    (rho sigma : Op (R × S)) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef) :
    (∀ (n : ℕ), 0 < n → ∀ W : Op (Fin n → R), copyPermutationInvariant W → Contractive W →
      ∃ U : Matrix.unitaryGroup R ℂ,
        (fidelityFactor n (dimensionParameter R S) *
          rootFidelity (liftFirst W * groupedPower rho n * (liftFirst W)ᴴ)
            (groupedPower sigma n)) ^ ((n : ℝ)⁻¹) ≤
        rootFidelity rho (liftFirst (U : Op R) * sigma * (liftFirst (U : Op R))ᴴ)) ∧
    (∀ W : (k : ℕ) → Op (Fin (k+1) → R),
      (∀ k, copyPermutationInvariant (W k) ∧ (W k).PosSemidef ∧ Contractive (W k)) →
      Filter.limsup (fun k =>
        (rootFidelity (liftFirst (W k) * groupedPower rho (k+1) * (liftFirst (W k))ᴴ)
          (groupedPower sigma (k+1))) ^ (((k+1 : ℕ) : ℝ)⁻¹)) atTop ≤
      sSup {v : ℝ | ∃ U : Matrix.unitaryGroup R ℂ,
        v = rootFidelity rho (liftFirst (U : Op R) * sigma * (liftFirst (U : Op R))ᴴ)}) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
