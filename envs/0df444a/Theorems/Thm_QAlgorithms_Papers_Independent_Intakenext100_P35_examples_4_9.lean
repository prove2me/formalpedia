-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_examples_4_9
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.examples_4_9
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:23:50.87638+00:00
-- url     : https://prove2.me/theorems/87a1ab22-634c-49ad-9086-4d38d5b7d9f0
-- title:
--   Examples 4.9
-- statement:
--   For $0<\psi<\pi$, $0<\phi<\pi-\psi$, and $\lambda\in\Sigma_\phi$, the resolvent lies in $\mathcal H_\psi$ with norm at most $C_{\phi,\psi}/|\lambda|$. If $0<\gamma<\pi/(2\psi)$, $\lambda\ne0$, and $|\arg\lambda|+\gamma\psi<\pi/2$, then $e_{\gamma,\lambda}(z)=e^{-\lambda z^\gamma}$ belongs to $\mathcal H_\psi$ and
--
--   $$\|e'_{\gamma,\lambda}\|_{H^1(\Sigma_\psi)}=\|e'_{1,\lambda}\|_{H^1(\Sigma_{\gamma\psi})}\le\int_{\partial\Sigma_{\gamma\psi}}|\lambda|e^{-\operatorname{Re}(\lambda z)}|dz|\le\frac1{\cos(\arg\lambda+\gamma\psi)}+\frac1{\cos(\arg\lambda-\gamma\psi)}.$$
--
--   These estimates provide elementary symbols for the H-calculus.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 21, Examples 4.9

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Examples 4.9, arXiv:2202.03143v1, PDF page(s) 21, 22. Source correction: The omitted lambda range and unbound phi on p.22 are made explicit by the decay-sector condition from the plan. Constants precede lambda. The line integral is expanded as its two positive radial integrals. Source correction needs independent moderation. -/
theorem examples_4_9
:
    (∀ psi phi : ℝ, 0 < psi → psi < Real.pi → 0 < phi → phi < Real.pi - psi →
      ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ openSectorDomain phi,
        HardySobolevClass psi (resolventSymbol lam) ∧
        hSize psi (resolventSymbol lam) ≤ ENNReal.ofReal (C / ‖lam‖)) ∧
    (∀ psi gamma : ℝ, 0 < psi → psi < Real.pi → 0 < gamma →
      gamma < Real.pi / (2 * psi) → ∀ lam : ℂ, lam ≠ 0 →
      |Complex.arg lam| + gamma * psi < Real.pi / 2 →
      HardySobolevClass psi (fun z => Complex.exp (-lam * z ^ (gamma : ℂ))) ∧
      hardySize psi (deriv (fun z => Complex.exp (-lam * z ^ (gamma : ℂ)))) =
        hardySize (gamma * psi) (deriv (fun z => Complex.exp (-lam * z))) ∧
      hardySize psi (deriv (fun z => Complex.exp (-lam * z ^ (gamma : ℂ)))) ≤
        (∫⁻ t, ENNReal.ofReal (‖lam‖ * Real.exp
          (-(lam * ((t : ℂ) * Complex.exp (Complex.I * (gamma * psi)))).re)) +
          ENNReal.ofReal (‖lam‖ * Real.exp
          (-(lam * ((t : ℂ) * Complex.exp (-Complex.I * (gamma * psi)))).re))
          ∂positiveVolume) ∧
      (∫⁻ t, ENNReal.ofReal (‖lam‖ * Real.exp
          (-(lam * ((t : ℂ) * Complex.exp (Complex.I * (gamma * psi)))).re)) +
          ENNReal.ofReal (‖lam‖ * Real.exp
          (-(lam * ((t : ℂ) * Complex.exp (-Complex.I * (gamma * psi)))).re))
          ∂positiveVolume) ≤ ENNReal.ofReal
          (1 / Real.cos (Complex.arg lam + gamma * psi) +
           1 / Real.cos (Complex.arg lam - gamma * psi))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
