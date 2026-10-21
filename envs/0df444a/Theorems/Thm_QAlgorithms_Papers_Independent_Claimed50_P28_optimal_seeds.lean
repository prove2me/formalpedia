-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P28_optimal_seeds
-- name    : QAlgorithms.Papers.Independent.Claimed50.P28.optimal_seeds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:23:05.361182+00:00
-- url     : https://prove2.me/theorems/1a9c50b9-4c00-483b-9452-e9ac31e710d7
-- title:
--   Explicit attaining square-root seeds and completeness
-- statement:
--   For $d\ge1$, let $\psi$ be any unit vector, let $K$ denote operations, channels or unital channels, and define
--
--   $$\Psi_K=\sqrt{(1-\beta_K)I/d+\beta_K|\psi\rangle\langle\psi|},\qquad\Pi_0=d|\Psi_K\rangle\!\rangle\langle\!\langle\Psi_K|,$$
--   $$\beta_{\mathcal Q}=\sqrt{\frac{d+1}{d^2+1}},\quad\beta_{\mathcal C}=\sqrt{\frac{d+1}{2+\sqrt2(d^2-1)}},\quad\beta_{\mathcal U}=0.$$
--
--   Each $\Psi_K$ is positive with Hilbert–Schmidt norm one, the seed is positive of trace $d$, and
--
--   $$\operatorname{Tr}[(\Psi_K\Psi_K^\dagger)^2]=\frac{1+(d-1)\beta_K^2}{d}.$$
--
--   Its Haar tester is complete on the required complex target span, has an attaining dual, and is realized with the normalized maximally entangled input and physical POVM density $d\Pi$. For $d\ge2$, $A=\beta_K^2/(d+1)$ gives respectively $1/(d^2+1)$, $1/(2+\sqrt2(d^2-1))$, and $0$. At $d=1$ purity and loss both equal one. These formulas correct the printed channel beta and channel purity and the printed unital purity; the corrections are separately recorded, not silently attributed to the page.
-- source:
--   Optimal quantum tomography for states, measurements, and transformations, arXiv:0806.1172v1, PDF p. 4, (35)–(36), corrected as documented

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P28

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Claimed50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted aliases/pairing; unrelated short-name collisions are not reused.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

/-- PDF pp.3–4, (33)–(36): explicit seeds, purity, attaining dual and target completeness.
Printed channel beta: [(d-1)(2+sqrt(2)(d²-1))]^(-1/2); changed to
sqrt((d+1)/(2+sqrt(2)(d²-1))) to match A=beta²/(d+1) and the optimizer in (33).
Printed channel purity: (sqrt(2)(d²-1)+3)/(d(sqrt(2)(d²-1)+2)); changed to
(2+(sqrt(2)+1)(d²-1))/(d(2+sqrt(2)(d²-1))) by (36)'s purity identity.
Printed unital purity: 1; changed to 1/d because beta=0 gives Psi=I/sqrt(d).
At d=1 the purity and minimum are 1 and no A-ratio is asserted. -/
theorem optimal_seeds {d : ℕ} (hd : 0 < d)
    (haar : Measure (SU d)) (hhaar : IsProbabilityHaar haar)
    (K : TomographyDomain) (psi : EuclideanSpace ℂ (Fin d)) (hpsi : QAlgorithms.IsState psi) :
    let Psi := seedMatrix K psi
    let beta := optimalBeta d K
    let P := fun _ : Fin 1 => optimalSeed K psi
    0 ≤ beta ∧ beta ≤ 1 ∧ Psi.PosSemidef ∧ hsSquared Psi = 1 ∧ Seeds P ∧
    (Psi * Psiᴴ * (Psi * Psiᴴ)).trace.re = (1 + ((d : ℝ) - 1) * beta^2) / (d : ℝ) ∧
    Attains haar K psi ∧
    (2 ≤ d → coefficientA P = beta^2 / ((d : ℝ) + 1) ∧
      coefficientA P = (match K with
        | .operations => 1 / ((d : ℝ)^2 + 1)
        | .channels => 1 / (2 + Real.sqrt 2 * ((d : ℝ)^2 - 1))
        | .unital => 0)) ∧
    (d = 1 → (Psi * Psiᴴ * (Psi * Psiᴴ)).trace.re = 1 ∧ optimum d K = 1) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P28

end
