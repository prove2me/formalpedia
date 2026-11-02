-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P58_appendix_annuli
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P58.appendix_annuli
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:00:29.743347+00:00
-- url     : https://prove2.me/theorems/ef98fabd-23e6-4c71-b1b5-3944b2c12982
-- title:
--   Nontrivial annular-boundary stationary surfaces
-- statement:
--   For each of the conformal and compactified D3 reduced models, there exist radii $0<R_i<R_e$ and a continuous direct profile $z:[R_i,R_e]\to\mathbb R$, twice differentiable in the interior, such that
--
--   $$
--   z(R_i)=z(R_e)=0,\qquad z(t)>0\quad(R_i<t<R_e).
--   $$
--
--   In the compactified model $z(t)<1$ in the interior. The profile satisfies the Euler–Lagrange equation of $\int t z^{-3}\sqrt{B(z)+z'(t)^2}\,dt$, where $B(z)=1$ in the conformal model and $B(z)=1-z^4$ in the compactified model. Rotating this graph gives a stationary surface ending on two distinct concentric boundary circles.
--
--   The radii are existential rather than arbitrary prescribed inputs. The result asserts stationarity and nontrivial annular boundary topology, and does not assert global minimality or turn the conjectural green-curve interpretation into a universal statement.
-- source:
--   Topological Entanglement Entropy and Holography, arXiv:0805.1891v2, PDF p. 11, §3.2 and Appendix A, pp.22–25

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P58

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P58

open Set Filter MeasureTheory

open scoped Topology

/-- PDF pp.8--9,11,22--25: nontrivial annular-boundary stationary surfaces exist
in the conformal and compactified D3 reduced models. The radii are existential,
not arbitrary prescribed radii. No trajectory is declared globally minimizing. -/
theorem appendix_annuli :
    ∀ m : RotationalModel, (m = .conformal ∨ m = .d3) →
      ∃ (Ri Re : ℝ) (Z : ℝ → ℝ), IsAnnulus m Ri Re Z := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P58

end
