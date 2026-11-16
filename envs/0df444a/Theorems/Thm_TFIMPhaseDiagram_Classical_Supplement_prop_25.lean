-- Prove2me | Theorems.Thm_TFIMPhaseDiagram_Classical_Supplement_prop_25
-- name    : TFIMPhaseDiagram.Classical.Supplement.prop_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:03:31.885621+00:00
-- url     : https://prove2.me/theorems/e36e7e82-c5d9-4106-ad27-75ec9e92910f
-- title:
--   Proposition 25 — Both path-space LDPs and the exact tilted average law
-- statement:
--   Fix $b,\eta>0$ with $(b/\eta)\tanh\eta>1$. For independent paths with law $\nu_\eta$, let $\tilde\rho_n$ be the law of their average and set $F(x)=b\|x\|^2/2$. Then $\rho_n=T_{nF}\tilde\rho_n$ is exactly the law of the average under $\mu_n$. The two sequences satisfy norm-topology large deviation principles at speed $n$, with respective rates
--   $$
--   \tilde I(x)=\sup_f\{\langle f,x\rangle-\Lambda_\eta(f)\},\qquad
--   J(x)=I(x)-\inf I,\quad I(x)=\tilde I(x)-F(x).
--   $$
--   For every $x\in L^2(S)$,
--   $$I(x)\ge-\Phi_{b,\eta}(bx).$$
--   The statement also records measurability of the spin-path map, existence and strict positivity of its exponential moments, and finiteness of the normalizing rate minimum. These certify the intended path laws and exponential tilts. Both LDP predicates include the probability-law, lower semicontinuity and nonnegative-rate requirements of Definition 24.
--
--   Differences from the source:
--   - encoding: L² spin law, finite exponential moments, and real normalizing infimum used in the proof → explicit path-map measurability, moment integrability and positivity, and a finite extended-real infimum; reason: certifies that Lean push-forward, integral and extended subtraction defaults do not replace the source quantities
--   - encoding: norm-topology LDPs for source indices n≥1 → the published metric LDP on independent coordinate realizations indexed by k+1; reason: same laws and norm topology, with unchanged asymptotic speed
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026); pinned source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, pp. 15-16, Proposition 25

import Definitions.Def_TFIMPhaseDiagram_Classical_Supplement_deviations

set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators ENNReal
noncomputable section

namespace TFIMPhaseDiagram.Classical.Supplement
attribute [local instance] Classical.propDecidable

/-- Proposition 25, pp.15–16. The path-map and integrability clauses certify that the
actual expectations and push-forwards are used, rather than Lean's defaults. -/
theorem prop_25 (b η : ℝ) (h : supercritical b η) :
    Measurable pathL2 ∧
    (∀ f : CircleL2, Integrable (fun σ => Real.exp (inner ℝ f σ)) (nuL2 η) ∧
      0 < ∫ σ, Real.exp (inner ℝ f σ) ∂nuL2 η) ∧
    (∀ n : ℕ, 0 < n → tiltedAverageLaw b η n = Measure.map averageL2 (cwLaw b η n)) ∧
    HasNormLDP (averageLaw η) (cramerRate η) ∧
    HasNormLDP (tiltedAverageLaw b η) (cwRate b η) ∧
    (∃ a : ℝ, rateMinimum b η = a) ∧
    (∀ x : CircleL2, (-(phi b η (b • x)) : ℝ) ≤ unnormalizedRate b η x) := by sorry

end TFIMPhaseDiagram.Classical.Supplement
