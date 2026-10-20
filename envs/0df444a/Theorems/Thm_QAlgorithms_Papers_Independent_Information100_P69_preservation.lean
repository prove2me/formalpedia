-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_preservation
-- name    : QAlgorithms.Papers.Independent.Information100.P69.preservation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:04:01.013183+00:00
-- url     : https://prove2.me/theorems/e6aa6bb3-8cee-4640-a352-77e760df6787
-- title:
--   Preservation of a faithful reference state
-- statement:
--   Fix faithful density matrices $\tau$ on $A$ and $\omega$ on $B$. The full family
--   $$\mathcal F_n^{\tau\to\omega}=\{M\text{ CPTP}:M(\tau^{\otimes n})=\omega^{\otimes n}\}$$
--   satisfies F1–F5 with those witnesses. For every density matrix $\rho$ on $B$, the replacer target $R_\rho$ satisfies, for $n\ge1$ and $0<\varepsilon<1$,
--   $$E_n=nD(\rho\|\omega),\qquad\beta_{\varepsilon,n}=\beta_\varepsilon^{\rm st}(\rho^{\otimes n}\|\omega^{\otimes n}),\qquad R_{\mathcal F}(R_\rho)=D(\rho\|\omega).$$
--   Here $\beta_\varepsilon^{\rm st}$ minimizes state alternative acceptance over effects accepting the target with probability at least $1-\varepsilon$. These are exact state-preservation benchmarks.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 21, Proposition 19

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Proposition 19, faithful-state preservation and exact replacer benchmarks, PDF pp.21–22. -/
theorem preservation [Nonempty A] [Nonempty B] (tau : Matrix A A ℂ) (omega : Matrix B B ℂ)
    (htau : Faithful tau) (homega : Faithful omega) :
    Admissible (preservingFamily tau omega) omega ∧ Additional (preservingFamily tau omega) tau ∧
    ∀ rho : Matrix B B ℂ, IsDensityMatrix rho →
      (∀ n, 1 ≤ n → resourceEntropy (power (replacer rho) n) (preservingFamily tau omega n) =
        (n:ℝ≥0∞)*entropy rho omega) ∧
      (∀ n, 1 ≤ n → ∀ eps : ℝ, 0 < eps → eps < 1 →
        beta (power (replacer rho) n) (preservingFamily tau omega n) eps =
          stateBeta (matrixPower rho n) (matrixPower omega n) eps) ∧
      entropy rho omega < ⊤ ∧
      rate (replacer rho) (preservingFamily tau omega) = (entropy rho omega).toReal := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
