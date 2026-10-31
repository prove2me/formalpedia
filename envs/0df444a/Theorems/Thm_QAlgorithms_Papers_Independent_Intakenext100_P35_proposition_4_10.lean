-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_proposition_4_10
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.proposition_4_10
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:24:09.328946+00:00
-- url     : https://prove2.me/theorems/a0f4b5cd-6e0c-42cf-9e01-9989da830176
-- title:
--   Proposition 4.10
-- statement:
--   Let $g$ be a Bernstein function. For $s>2$ and $\lambda\in\mathbb C_+$, $(\lambda+g)^{-1}\in\mathcal D_s$ with norm at most $C_s/|\lambda|$, where $C_s$ depends only on $s$. If $0<\psi<\pi/2$, $\psi<\phi<\pi$, and $\lambda\in\Sigma_{\pi-\phi}$, then $(\lambda+g)^{-1}\in\mathcal H_\psi$ and
--
--   $$\|(\lambda+g)^{-1}\|_{\mathcal H_\psi}\le\frac2{|\lambda|}\left(\frac1{\sin(\min(\phi,\pi/2))}+\frac2{\cos\psi\,\sin^2((\phi-\psi)/2)}\right).$$
--
--   The constants are uniform over the Bernstein symbol.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 22, Proposition 4.10

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Proposition 4.10, arXiv:2202.03143v1, PDF page(s) 22. -/
theorem proposition_4_10
:
    (∀ s : ℝ, 2 < s → ∃ C : ℝ, 0 < C ∧ ∀ g, HolomorphicBernstein g → ∀ lam ∈ hp,
      D s (fun z => (lam + g z)⁻¹) ∧
      dSize s (fun z => (lam + g z)⁻¹) ≤ ENNReal.ofReal (C / ‖lam‖)) ∧
    (∀ psi phi : ℝ, 0 < psi → psi < Real.pi / 2 → psi < phi → phi < Real.pi →
      ∀ g, HolomorphicBernstein g → ∀ lam ∈ openSectorDomain (Real.pi - phi),
      HardySobolevClass psi (fun z => (lam + g z)⁻¹) ∧
      hSize psi (fun z => (lam + g z)⁻¹) ≤ ENNReal.ofReal
        (2 * (1 / Real.sin (min phi (Real.pi / 2)) +
          2 / (Real.cos psi * Real.sin ((phi - psi) / 2) ^ 2)) / ‖lam‖)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
