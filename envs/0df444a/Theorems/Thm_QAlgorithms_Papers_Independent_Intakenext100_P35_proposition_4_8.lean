-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_proposition_4_8
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.proposition_4_8
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:23:25.785004+00:00
-- url     : https://prove2.me/theorems/89d17bc4-8cc9-49c9-86aa-58abf19e0949
-- title:
--   Proposition 4.8
-- statement:
--   Each $\mathcal H_\psi$, $0<\psi<\pi$, is a Banach algebra. For $0<\psi_1,\psi_2<\pi$, principal-power composition gives an onto isometric algebra homomorphism
--
--   $$\mathcal H_{\psi_1}\longrightarrow\mathcal H_{\psi_2},\qquad f\longmapsto\bigl[z\mapsto f(z^{\psi_1/\psi_2})\bigr].$$
--
--   This transfers the half-plane theory to arbitrary sectors.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 21, Proposition 4.8

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Proposition 4.8, arXiv:2202.03143v1, PDF page(s) 21. -/
theorem proposition_4_8
:
    (∀ psi : ℝ, 0 < psi → psi < Real.pi →
      BanachAlgebraSymbols (openSectorDomain psi) (HardySobolevClass psi) (hSize psi)) ∧
    (∀ psi1 psi2 : ℝ, 0 < psi1 → psi1 < Real.pi → 0 < psi2 → psi2 < Real.pi →
      (∀ f, HardySobolevClass psi1 f → HardySobolevClass psi2 (powerPull (psi1 / psi2) f) ∧
        hSize psi2 (powerPull (psi1 / psi2) f) = hSize psi1 f) ∧
      (∀ g, HardySobolevClass psi2 g → ∃ f, HardySobolevClass psi1 f ∧
        EqOn (powerPull (psi1 / psi2) f) g (openSectorDomain psi2))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
