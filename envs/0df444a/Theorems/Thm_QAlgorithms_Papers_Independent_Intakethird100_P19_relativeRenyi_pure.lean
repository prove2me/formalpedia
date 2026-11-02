-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_relativeRenyi_pure
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.relativeRenyi_pure
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:32:49.312592+00:00
-- url     : https://prove2.me/theorems/9f301ad8-703f-4f7a-844f-65ecd7fc4f60
-- title:
--   Theorem 4: relative Renyi entanglement of pure states
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces with fixed product bases and positive local dimensions. States are positive semidefinite operators of trace one; pure kets have norm one. Let $\psi$ be a bipartite pure state and $0\le\alpha\le2$. Let $E_{R,\alpha}(\rho)=\inf_{\sigma\in\mathcal S}D_\alpha(\rho\Vert\sigma)$, where $D_\alpha$ is the Petz divergence in bits and $\mathcal S$ contains all separable density matrices. Then
--
--   $$E_{R,\alpha}(\psi)=E_{1/\alpha}(\psi),\qquad 1/0:=+\infty.$$
--
--   The order-one branch is Umegaki relative entropy. Order zero uses support projectors, and $E_\infty=-\log_2\lambda_{\max}$ for the largest squared Schmidt coefficient. Support violations have extended value $+\infty$.
--
--   This supplies a closed expression without full-support assumptions.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 10, Theorem 4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P19

noncomputable section

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P19

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P19 (Bip)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P19 (epr)

/-- Theorem 4, PDF p.10; proof pp.26-28: Petz relative Renyi entanglement
on a pure state equals Schmidt entropy at reciprocal order, with 1/0=infinity.
The reversed order interval in the prose on p.24 is not used. -/
theorem relativeRenyi_pure {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (psi : UnitBipartiteKet a b) (alpha : ℝ) (h0 : 0 ≤ alpha) (h2 : alpha ≤ 2) :
    relativeRenyi alpha psi.rho =
      ENNReal.ofReal (schmidtRenyi (ENNReal.ofReal alpha)⁻¹ psi.ket) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end
