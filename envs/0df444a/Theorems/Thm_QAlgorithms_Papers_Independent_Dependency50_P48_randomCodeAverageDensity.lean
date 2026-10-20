-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P48_randomCodeAverageDensity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P48.randomCodeAverageDensity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:46:33.956881+00:00
-- url     : https://prove2.me/theorems/c49b4ad4-3c0a-4051-9966-14ea045afacf
-- title:
--   Random transmission codes approach the prescribed iid mean density
-- statement:
--   Let $\rho$ be a normalized density matrix on a finite nonempty register $P$, and let $\mathcal N$ have a fixed isometric dilation into finite nonempty $Q\otimes E$. For every $\epsilon,\delta>0$ and every sufficiently large positive $n$, there are a common positive logical dimension $\kappa$, a finite probability law $(p_\beta)$, and isometric transmission codes $(V_\beta,D_\beta)$ with CPTP decoders and
--
--   $$\frac{\log_2\kappa}{n}\ge I_c(\rho,\mathcal N)-\delta.$$
--
--   Let $F_\beta$ be the squared entanglement fidelity at the maximally mixed logical input, and let $\rho_\beta=V_\beta V_\beta^\dagger/\kappa$ be the uniform mixture of that code's orthonormal codewords. Then
--
--   $$\sum_\beta p_\beta F_\beta\ge1-\epsilon,\qquad\left\|\sum_\beta p_\beta\rho_\beta-\rho^{\otimes n}\right\|_1\le\epsilon.$$
--
--   All codes are valid and have the same dimension. Fidelity is averaged over both randomizations, including rare failed draws completed by valid fallback codes; success is not demanded of every sampled code. The norm is the full trace norm. This is the asymptotic ensemble conclusion of Appendix D.
-- source:
--   The private classical capacity and quantum capacity of a quantum channel, arXiv:quant-ph/0304127v6, PDF p. 18, Appendix D, main conclusion, pp.18–20

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P48

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P67 (dilationPower)

attribute [local instance] Classical.propDecidable

variable {P Q E X H : Type*}

variable [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

variable [Fintype E] [DecidableEq E] [Fintype X] [DecidableEq X]

variable [Fintype H] [DecidableEq H]

/-- Appendix D, PDF pp.18–20 (announced p.15): valid isometric codes of the
same dimension have high AVERAGE fidelity and mean density approaching rho^n
in TRACE NORM. Both randomizations and failed draws are averaged. -/
theorem randomCodeAverageDensity [Nonempty P] [Nonempty Q] [Nonempty E]
    (U : Matrix (Q × E) P ℂ) (hU : IsDilation U)
    (rho : Matrix P P ℂ) (hrho : IsDensityMatrix rho) :
    ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
      ∃ k : ℕ, ∃ hk : 0 < k,
        coherentInformation (receiver U) rho - delta ≤ Real.logb 2 (k : ℝ) / (n : ℝ) ∧
        ∃ L : ℕ, 0 < L ∧ ∃ prob : Fin L → ℝ,
          (∀ b, 0 ≤ prob b) ∧ (∑ b, prob b = 1) ∧
          ∃ codes : Fin L → IsometricCode (Fin n → P) (Fin n → Q) k,
            1 - eps ≤ ∑ b, prob b * (codes b).fidelity hk (receiver (dilationPower U n)) ∧
            traceNorm ((∑ b, (prob b : ℂ) • (codes b).density) - densityPower rho n) ≤ eps := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P48

end
