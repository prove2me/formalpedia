-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P45_direct_quantum_stein
-- name    : QAlgorithms.Papers.Independent.Claimed50.P45.direct_quantum_stein
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:14:41.306756+00:00
-- url     : https://prove2.me/theorems/9b8fd730-17e5-48a5-a3d5-15ff68354a42
-- title:
--   Direct quantum Stein lemma: a single entropy-achieving sequence
-- statement:
--   Let $\rho$ and $\sigma$ be arbitrary density operators on one finite-dimensional complex Hilbert space. Set $\rho_n=\rho^{\otimes n}$ and $\sigma_n=\sigma^{\otimes n}$. A test $A_n$ accepts the null hypothesis $\rho_n$ and satisfies $0\leq A_n\leq I_n$. Define its two errors by $\alpha_n(A_n)=\operatorname{Tr}[\rho_n(I_n-A_n)]$ and $\beta_n(A_n)=\operatorname{Tr}[\sigma_nA_n]$. Let $D(\rho\|\sigma)$ be support-aware Umegaki relative entropy in natural units.
--
--   There is one sequence of tests $(A_n)_{n\geq1}$ such that
--
--   $$
--   \lim_{n\to\infty}\alpha_n(A_n)=0,\qquad
--   \limsup_{n\to\infty}\frac{1}{n}\log\beta_n(A_n)\leq-D(\rho\|\sigma).
--   $$
--
--   The logarithm of zero is $-\infty$. Thus if $D(\rho\|\sigma)=+\infty$, the beta rate has limit superior $-\infty$.
--
--   This is the direct, existence part of the quantum Stein lemma. It asserts attainment of the entropy bound by a single sequence; it contains no converse assertion.
--
--   **Formalization Note** The sequence is a dependent function of $k$, whose effects act on exactly $k+1$ tensor copies.
-- source:
--   On Error Exponents in Quantum Hypothesis Testing, arXiv:quant-ph/0206151v3, PDF p. 3, Equation (10); re-proved on PDF p.9

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P45

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P45

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter Topology QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (positiveProjection)

open QAlgorithms.Papers.Independent.Dependency50.P28
  (LE pinch logNonnegativeExtended typeI accept scaled TestSequence)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I : Type} [Fintype I] [DecidableEq I]

/-- PDF p.3, (10), explicitly re-proved after Theorem 3 on p.9: one sequence
of valid effects has vanishing type-I error and beta limsup rate at most -D.
At D=+infinity the upper rate is -infinity. No converse is included. -/
theorem direct_quantum_stein
    (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    ∃ T : TestSequence I,
      Tendsto (fun k : ℕ => typeI rho (k + 1) (T k).1) atTop (𝓝 0) ∧
      limsup (fun k : ℕ => scaled k (logNonnegativeExtended
        (accept sigma (k + 1) (T k).1))) atTop ≤
        -(QuantumLoss.umegakiEntropy rho sigma hrho hsigma : EReal) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P45

end
