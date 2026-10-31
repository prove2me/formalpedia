-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P08_typeII_optimalDisplacement
-- name    : QAlgorithms.Papers.Independent.Intake100.P08.typeII_optimalDisplacement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:48:56.516579+00:00
-- url     : https://prove2.me/theorems/d5ff86c2-5557-49e5-be26-b57dea62aa47
-- title:
--   Optimal displacement receiver with efficiency and dark counts
-- statement:
--   Let the two normalized coherent signals be $|\pm\alpha\rangle$ in the completed one-mode Fock space, with known real $\alpha\ge0$ and equal priors. Fix detector efficiency $0\le\eta\le1$ and dark-count parameter $\nu\ge0$. A fixed complex displacement $D(\delta)$ is followed by the on/off POVM whose no-click weights in the number basis are $e^{-\nu}(1-\eta)^n$. Decode off as minus and on as plus. Its average Bayesian error is
--
--   $$
--   P_D(\delta)=\frac12-e^{-\nu-\eta(\alpha^2+|\delta|^2)}\sinh(2\eta\alpha\operatorname{Re}\delta).
--   $$
--
--   The photon-number laws are normalized, the photon-number and detector series are summable, and $0\le P_D(\delta)\le1$. If $\alpha=0$ or $\eta=0$, then $P_D(\delta)=1/2$ for every displacement. If $\alpha>0$ and $\eta>0$, the global minimizer over all complex displacements is unique, is real, and satisfies
--
--   $$
--   \gamma_{\rm opt}>\alpha,\qquad
--   \alpha=\gamma_{\rm opt}\tanh(2\eta\alpha\gamma_{\rm opt}),\qquad
--   P_D(\gamma_{\rm opt})<P_D(\alpha).
--   $$
--
--   Thus replacing the Kennedy displacement by the actual optimal displacement strictly improves its error in the nondegenerate regime. The optimizer is obtained from the operational error; the root equation is concluded rather than assumed to imply optimality.
--
--   **Formalization Note** The accepted coherent vectors and Weyl displacements act on the full countable Fock space. Their realization guards are conclusions, so their off-domain fallback values are never used as physical states or devices.
-- source:
--   Discrimination of the binary coherent signal: Gaussian-operation limit and simple non-Gaussian near-optimal receivers, arXiv:0706.1038v3, PDF p. 5, Section III, Eqs. (18), (19), (23), (24)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P08

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P08

open MeasureTheory

open scoped BigOperators

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock fockKet coherentKet coherentCoefficient CoherentRealized
   displacement DisplacementRealized)

/-- PDF pp.4--5, Eqs.(18),(19),(23),(24): exact displacement-receiver error
and its global optimum, with efficiency and dark counts retained. Complex
competitors are allowed. The root equation is a conclusion about the actual
unique global minimizer; no stationary point is assumed optimal. At alpha=0
or eta=0 the error is exactly 1/2. Realization and summability guard all uses
of the accepted coherent/displacement total functions and infinite series. -/
theorem typeII_optimalDisplacement
    (alpha eta nu : ℝ) (halpha : 0 ≤ alpha)
    (heta : 0 ≤ eta) (hetaMax : eta ≤ 1) (hnu : 0 ≤ nu) :
    CoherentRealized ∧ DisplacementRealized ∧
    (∀ delta : ℂ,
      (∀ plus : Bool,
        let psi := displacement delta (coherentKet (signalAmplitude alpha plus))
        ‖psi‖ = 1 ∧ Summable (photonLaw psi) ∧
          (∑' n, photonLaw psi n) = 1 ∧
          Summable (fun n : ℕ => (1 - eta) ^ n * photonLaw psi n)) ∧
      displacementError alpha eta nu delta =
        1 / 2 - Real.exp (-nu - eta * (alpha ^ 2 + Complex.normSq delta)) *
          Real.sinh (2 * eta * alpha * delta.re) ∧
      0 ≤ displacementError alpha eta nu delta ∧
        displacementError alpha eta nu delta ≤ 1) ∧
    ((alpha = 0 ∨ eta = 0) → ∀ delta : ℂ,
      displacementError alpha eta nu delta = 1 / 2) ∧
    (0 < alpha → 0 < eta → ∃ gamma : ℝ,
      alpha < gamma ∧
      alpha = gamma * Real.tanh (2 * eta * alpha * gamma) ∧
      (∀ delta : ℂ, displacementError alpha eta nu (gamma : ℂ) ≤
        displacementError alpha eta nu delta) ∧
      (∀ delta : ℂ, displacementError alpha eta nu delta =
        displacementError alpha eta nu (gamma : ℂ) → delta = (gamma : ℂ)) ∧
      displacementError alpha eta nu (gamma : ℂ) <
        displacementError alpha eta nu (alpha : ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P08

end
