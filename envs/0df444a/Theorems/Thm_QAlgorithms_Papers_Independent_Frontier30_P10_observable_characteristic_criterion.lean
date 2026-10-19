-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P10_observable_characteristic_criterion
-- name    : QAlgorithms.Papers.Independent.Frontier30.P10.observable_characteristic_criterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:14:38.322287+00:00
-- url     : https://prove2.me/theorems/cde92eda-530e-4cc9-80e7-8acc424e3dec
-- title:
--   Operator-valued characteristic-function criterion
-- statement:
--   Let $\mathcal H$ be a nonzero separable complex Hilbert space carrying the source’s strongly continuous irreducible Weyl system, and $Z=\mathbb R^{2n}$ have the standard symplectic form $\Delta(w,z)=\sum_j(w_{j,y}z_{j,x}-w_{j,x}z_{j,y})$. Let $\phi:Z\to\mathcal B(\mathcal H)$ be any bounded-operator-valued function. It is the characteristic function of a normalized POVM $M$, meaning $\phi(w)=\int_Z e^{i\Delta(w,z)}M(dz)$ weakly, if and only if
--
--   $$
--   \phi(0)=I,\qquad
--   \phi\text{ is weakly continuous at }0,\qquad
--   [\phi(w_j-w_k)]_{j,k=1}^{m}\succeq0
--   \quad\text{for every finite tuple }(w_1,\ldots,w_m).
--   $$
--
--   Weak continuity tests every matrix element $\langle u,\phi(w)v\rangle$. Block positivity means that $\sum_{j,k}\langle v_j,\phi(w_j-w_k)v_k\rangle$ is real and nonnegative for every tuple of Hilbert vectors $v_1,\ldots,v_m$. This criterion characterizes actual observables without presupposing a density or Gaussian form.
-- source:
--   Entanglement-breaking channels in infinite dimensions, arXiv:0802.0235v1, PDF p. 8, Unnumbered: operator-valued characteristic-function criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P10

noncomputable section

open MeasureTheory

open scoped ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier30.P10

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Holevo, arXiv:0802.0235v1, PDF p.8, the three-condition operator-valued
characteristic-function criterion. Weak continuity means every matrix element
is continuous at zero; block positivity tests arbitrary finite vector tuples. -/
theorem observable_characteristic_criterion [SecondCountableTopology H] [Nontrivial H]
    {a : ℕ} (_W : WeylSystem H a) {n : ℕ} (phi : (Phase n → ℝ) → H →L[ℂ] H) :
    (∃ M : HilbertPOVM H (Phase n → ℝ), HasCharacteristic M phi) ↔
      phi 0 = ContinuousLinearMap.id ℂ H ∧
      (∀ u v : H, ContinuousAt (fun w => inner ℂ u (phi w v)) 0) ∧
      OperatorPositiveDefinite phi := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P10

end
