-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_conjectureOne
-- name    : QAlgorithms.Papers.Independent.Information100.P75.conjectureOne
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:10:03.908709+00:00
-- url     : https://prove2.me/theorems/2ceafb16-95d9-4472-b05a-81b782fa63b2
-- title:
--   The conjecture subspace has a density annihilator exactly above the threshold
-- statement:
--   For $\pi/2\le\beta\le\pi$, set
--
--   $$S_\beta=\operatorname{span}_{\mathbb C}\{\operatorname{diag}(1,e^{i\beta},0),\operatorname{diag}(0,1,e^{i\beta})\}.$$
--
--   For every integer $N\ge1$, with orthogonality taken in the Hilbert–Schmidt pairing,
--
--   $$\exists\rho\succeq0:\operatorname{Tr}\rho=1,\ \rho\in(S_\beta^{\otimes N})^\perp
--   \iff \frac\pi2+\frac\pi{2N}\le\beta\le\pi.$$
--
--   Both endpoints are included. This supplies the full content of the conjecture affirmed by Corollary 5.
-- source:
--   Parallel quantum channel discrimination and numerical ranges in tensor product subspaces, arXiv:2609.20781v1, PDF p. 5, Corollary 5; Conjecture 1, p.2

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P75

open Classical

open scoped ComplexConjugate ComplexOrder Matrix

open MeasureTheory

/-- Corollary 5, PDF p.5, Conjecture 1 p.2: inclusive threshold for a density in the
Hilbert–Schmidt orthogonal complement. The adjoint is explicit in the pairing. -/
theorem conjectureOne (N : ℕ) (hN : 1 ≤ N) (b : ℝ)
    (hb : Real.pi / 2 ≤ b) (hbp : b ≤ Real.pi) :
    (∃ R : Mat (Fin N → Fin 3), IsDensityMatrix R ∧
      ∀ X ∈ tensorPower (betaSpace b) N, (Rᴴ * X).trace = 0) ↔
    Real.pi / 2 + Real.pi / (2 * (N : ℝ)) ≤ b ∧ b ≤ Real.pi := by sorry

end QAlgorithms.Papers.Independent.Information100.P75

end
