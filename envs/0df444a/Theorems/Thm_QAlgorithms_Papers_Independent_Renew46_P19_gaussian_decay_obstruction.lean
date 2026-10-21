-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P19_gaussian_decay_obstruction
-- name    : QAlgorithms.Papers.Independent.Renew46.P19.gaussian_decay_obstruction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:28:16.060855+00:00
-- url     : https://prove2.me/theorems/18454b6f-9e53-40b6-81b4-f6773fecf130
-- title:
--   Gaussian obstruction and isotropic threshold
-- statement:
--   Let $n\ge1$, $\hbar>0$, $0\ne\psi\in L^2(\mathbb R^n)$, and $\phi\in L^2(\mathbb R^n)$ with $\|\phi\|_2=1$. If $C,a,b>0$ and the continuous normalized Wigner representative satisfies
--
--   $$
--   |W_\phi\psi(x,p)|\le C\exp\!\left(-\frac{a|x|^2+b|p|^2}{\hbar}\right)
--   $$
--
--   at every point, then $ab\le1$. Likewise, for $C,\epsilon>0$,
--
--   $$
--   |W_\phi\psi(z)|\le C e^{-|z|^2/\epsilon}\quad\hbox{for every }z
--   \quad\Longrightarrow\quad\epsilon\ge\hbar.
--   $$
--
--   The nonzero input and unit window exclude the trivial zero Wigner function. The result limits Gaussian concentration of vectors in a fixed window range.
-- source:
--   A new approach to the star-genvalue equation, arXiv:0808.0489v1, PDF p. 12, §6, (21) and its consequence

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P19

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Renew46.P19

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration coordinateDot)

open QAlgorithms.Papers.Independent.Claimed50.P37 (PhaseCoordinates Quadrature)

open QAlgorithms.Papers.Independent.Next46.P20
  (ConfigurationL2 PhaseL2 phasePosition phaseMomentum phasePoint)

open QAlgorithms.Papers.Independent.Claimed50.P05 (spectrumOf pointSpectrum)

open QAlgorithms.Papers.Independent.Frontier30.P10 (symplecticPair)

local notation "sigma" => fun {n : ℕ} (z w : PhaseCoordinates n) =>
  symplecticPair (Sum.elim (phasePosition z) (phaseMomentum z))
    (Sum.elim (phasePosition w) (phaseMomentum w))

/-- PDF p.12, (21) and its isotropic consequence: nonzero L2 input and a unit
L2 window. The printed y in the Gaussian envelope is read as p. -/
theorem gaussian_decay_obstruction {n : ℕ} (hn : 0 < n) (hbar : ℝ) (hhbar : 0 < hbar)
    (psi phi : ConfigurationL2 n) (hpsi : psi ≠ 0) (hphi : ‖phi‖ = 1) :
    (∀ C a b : ℝ, 0 < C → 0 < a → 0 < b →
      (∀ z : PhaseCoordinates n, ‖windowFormula hbar psi phi z‖ ≤ C * Real.exp
        (-((a * coordinateDot (phasePosition z) (phasePosition z) +
          b * coordinateDot (phaseMomentum z) (phaseMomentum z)) / hbar))) →
      a * b ≤ 1) ∧
    (∀ C epsilon : ℝ, 0 < C → 0 < epsilon →
      (∀ z : PhaseCoordinates n, ‖windowFormula hbar psi phi z‖ ≤
        C * Real.exp (-(radiusSquared z / epsilon))) → hbar ≤ epsilon) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P19

end
