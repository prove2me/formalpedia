-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P19_window_isometry_adjoint
-- name    : QAlgorithms.Papers.Independent.Renew46.P19.window_isometry_adjoint
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:22:24.048539+00:00
-- url     : https://prove2.me/theorems/70086f2e-4321-48e3-b892-1d52b9c706ff
-- title:
--   Normalized window isometry and its adjoint
-- statement:
--   Fix $n\ge1$, $\hbar>0$, and a Schwartz function $\phi$ on $\mathbb R^n$ with $\|\phi\|_2=1$. The normalized cross-Wigner transform
--
--   $$
--   W_\phi\psi(x,p)=(2\pi\hbar)^{-n/2}\int e^{-ip\cdot y/\hbar}\psi(x+y/2)\overline{\phi(x-y/2)}\,dy
--   $$
--
--   extends to a linear isometry from $L^2(\mathbb R^n)$ onto its range in $L^2(\mathbb R^{2n})$. For Schwartz $\Psi$, its Hilbert adjoint has the almost-everywhere formula
--
--   $$
--   W_\phi^*\Psi(x)=\left(\frac{2}{\pi\hbar}\right)^{n/2}\int_{\mathbb R^{2n}}e^{2ip\cdot(x-y)/\hbar}\phi(2y-x)\Psi(y,p)\,dy\,dp.
--   $$
--
--   This supplies the window embedding and its adjoint without interpreting oscillatory integrals of arbitrary L2 functions as Bochner integrals.
-- source:
--   A new approach to the star-genvalue equation, arXiv:0808.0489v1, PDF p. 5, §3, (12)–(14)

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

/-- PDF p.5, (12)–(14): the normalized Schwartz-window transform has its
L2 isometric extension and the displayed adjoint on Schwartz inputs. -/
theorem window_isometry_adjoint {n : ℕ} (hn : 0 < n) (hbar : ℝ) (hhbar : 0 < hbar)
    (phi : SchwartzMap (Configuration n) ℂ)
    (hphi : ‖phi.toLp 2 (volume : Measure (Configuration n))‖ = 1) :
    let phiL2 := phi.toLp 2 (volume : Measure (Configuration n))
    RealizesWindow hbar phiL2 (windowMap hbar phiL2) ∧
    Isometry (windowMap hbar phiL2) ∧
    (∀ Psi : SchwartzMap (PhaseCoordinates n) ℂ, ∀ᵐ x : Configuration n,
      (windowMap hbar phiL2).adjoint
        (Psi.toLp 2 (volume : Measure (PhaseCoordinates n))) x =
          adjointFormula hbar phi Psi x) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P19

end
