-- Prove2me | Theorems.Thm_TailRiskSharing_VaRConv_Supplement_theorem5_nonattainment_counterexample
-- name    : TailRiskSharing.VaRConv.Supplement.theorem5_nonattainment_counterexample
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:45:17.861306+00:00
-- url     : https://prove2.me/theorems/26b22558-06bf-414f-9a29-ffa7b751c0cc
-- title:
--   Theorem 5 (corrected: counterexample to attainment) — monetary tail agents need not admit an elliptical optimum
-- statement:
--   The attainment assertion of Theorem 5 is false without an additional regularity condition. On $\Omega=\mathbb R$, give the identity total risk $X(x)=x$ its standard symmetric Laplace law $P(dx)=\frac12e^{-|x|}\,dx$, with generator $\psi(s)=(1+s)^{-1}$. Take the full domain $\mathcal X=L^0$. Define
--
--   $$\rho_1(Y)=\mathrm{VaR}^R_{1/2}(Y)+\mathbf1_{\{\mathbb E[e^{2Y}]=\infty\}},\qquad \rho_2(Y)=\mathrm{VaR}^R_{e^{-1}/2}(Y).$$
--
--   These are real-valued monetary tail risk measures at levels $1/2$ and $e^{-1}/2$, respectively. The probability space is atomless, the full source domain assumptions hold, and $X\in\mathcal E_1(\psi)\subseteq\mathcal X$. Nevertheless,
--
--   $$V_\psi(X)=\frac12> -\infty,\qquad \sum_i\rho_i(X_i)>\frac12\quad\text{for every feasible jointly elliptical allocation}.$$
--
--   In particular no optimal allocation exists. For proportional coefficients $(c,1-c)$, $0\leq c\leq1$, the exact objective is
--
--   $$J_X(c,1-c)=1-c+\mathbf1_{\{c\geq1/2\}},$$
--
--   so (25) has no optimizer either. The comonotonic, jointly elliptical allocations with $c=1/2-1/(k+3)$ have costs $1/2+1/(k+3)$ for every integer $k\geq0$. They witness the infimum without smuggling attainment into a premise. Cash transfers cannot restore attainment since they sum to zero in the aggregate monetary objective.
--
--   This counterexample addresses all clauses requiring an optimizer, rather than restricting the theorem to bounded risks or assuming the desired minimizer. The analytic verification is retained in DISPROOF.md; the Lean item is a theorem target, not an already completed proof.
--
--   Differences from the source:
--   - correction: Theorem 5 asserts existence of an elliptical optimizer and an optimizer of (25) without continuity → an explicit two-agent Laplace counterexample satisfying every source premise, with finite infimum 1/2 and no optimizer in either problem; reason: rho_1(Y) = VaR^R_(1/2)(Y) + 1{E exp(2Y) is infinite} is monetary and half-tail; together with rho_2 = VaR^R_(exp(-1)/2), the simplex cost is 1-c+1{c>=1/2}, which never attains its infimum; DISPROOF.md verifies the full elliptical feasible class.
--   - encoding: (24) is written with min → EReal infimum and a separate predicate for global attainment; reason: a minimum cannot be assumed in the definition of the value of the problem whose attainment is under examination.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), pp. 22–24, Theorem 5, (24)–(29); explicit counterexample in local DISPROOF.md

import Mathlib
import Definitions.Def_TailRiskSharing_VaRConv_Setting
import Definitions.Def_TailRiskSharing_VaRTail_Setting
import Definitions.Def_TailRiskSharing_ComonoConv_Comonotone
import Definitions.Def_TailRiskSharing_VaRConv_Supplement_Domain
import Definitions.Def_TailRiskSharing_VaRConv_Supplement_EllipticalProblem
import Definitions.Def_TailRiskSharing_VaRConv_Supplement_Simplex

namespace TailRiskSharing.VaRConv.Supplement

open MeasureTheory Classical

/-- Theorem 5, pp.22–24: counterexample to attainment without a continuity assumption.
P is the standard symmetric Laplace law and X is the identity. The first agent charges
an extra unit exactly when E exp(2Y) is infinite. This charge is monotone, cash-invariant
and determined by every upper tail. See DISPROOF.md for the full analytic verification. -/
theorem theorem5_nonattainment_counterexample :
    let P : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-|x|) / 2))
    let ψ : ℝ → ℂ := fun s => (1 + (s : ℂ))⁻¹
    let dom : Set (ℝ → ℝ) := L0
    let X : ℝ → ℝ := id
    let εs : Fin 2 → ℝ := ![1 / 2, Real.exp (-1) / 2]
    let ρ : Fin 2 → (ℝ → ℝ) → ℝ :=
      ![fun Y => VaRR P (1 / 2) Y +
          (if Integrable (fun ω => Real.exp (2 * Y ω)) P then 0 else 1),
        VaRR P (Real.exp (-1) / 2)]
    IsProbabilityMeasure P ∧ IsAtomless P ∧ IsSourceDomain P dom ∧
    (∀ Y : ℝ → ℝ, IsEllipticalScalar P ψ Y → Y ∈ dom) ∧
    X ∈ dom ∧ IsEllipticalScalar P ψ X ∧
    (∀ i, 0 < εs i ∧ εs i ≤ 1 / 2) ∧
    (∀ i, TailRiskSharing.VaRTail.IsMonetary P dom (ρ i) ∧
      TailRiskSharing.VaRTail.IsTailRiskMeasure P dom (εs i) (ρ i)) ∧
    (⊥ : EReal) < ellipticalValue P dom ψ ρ X ∧
    ellipticalValue P dom ψ ρ X = ((1 / 2 : ℝ) : EReal) ∧
    (∀ Xs ∈ EllipticalAllocations P dom ψ 2 X, (1 / 2 : ℝ) < ∑ i, ρ i (Xs i)) ∧
    (¬ ∃ Xs, IsEllipticalOptimal P dom ψ ρ X Xs) ∧
    (∀ c ∈ Simplex 2, simplexObjective ρ X c =
      1 - c 0 + (if c 0 < 1 / 2 then 0 else 1)) ∧
    (¬ ∃ c, IsSimplexOptimizer ρ X c) ∧
    (∀ k : ℕ,
      let c : Fin 2 → ℝ := ![1 / 2 - 1 / ((k : ℝ) + 3), 1 / 2 + 1 / ((k : ℝ) + 3)]
      c ∈ Simplex 2 ∧
      affineAllocation X 0 c ∈ EllipticalAllocations P dom ψ 2 X ∧
      (∀ i, TailRiskSharing.ComonoConv.Comonotone P (affineAllocation X 0 c i) X) ∧
      simplexObjective ρ X c = 1 / 2 + 1 / ((k : ℝ) + 3))
    := by sorry

end TailRiskSharing.VaRConv.Supplement
