-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P46_gaussianExponentFormulas
-- name    : QAlgorithms.Papers.Independent.Renew46.P46.gaussianExponentFormulas
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:57:11.372683+00:00
-- url     : https://prove2.me/theorems/0ffe6a39-d402-4bc4-95fd-53689f6117cb
-- title:
--   §V: explicit Gaussian-prior exponent functionals, (42)–(43)
-- statement:
--   Fix the noiseless full-Fock coherent-state channel, a finite energy $E>0$ and the circular Gaussian prior $G_E$. Let $p\in[0,1/E)$, and let $T_{E,p}=\int e^{p(|z|^2-E)}|z\rangle\langle z|\,G_E(dz)$. The weighted integral genuinely converges and, with $\tau_t$ thermal of photon mean $t$,
--
--   $$T_{E,p}=\frac{e^{-pE}}{1-pE}\tau_{E/(1-pE)}.$$
--
--   The coherent squared overlap is $e^{-|z-w|^2}$. For the actual trace and overlap-integral functionals of Section IV,
--
--   $$\mu(G_E,s,p)=(1+s)pE+\log\big[(1+E-pE)^{1+s}-E^{1+s}\big]\quad(0\le s\le1),$$
--   $$\widetilde\mu(G_E,s,p)=s\left\{2pE+\log\left[1+p^2E^2-2pE+\frac{2E(1-pE)}s\right]\right\}\quad(s\ge1).$$
--
--   These are evaluations of the actual operators and integrals, rather than definitions by the claimed closed forms.
-- source:
--   On Quantum Communication Channels with Constrained Inputs, arXiv:quant-ph/9705054v1, PDF p. 13, §V: explicit Gaussian-prior exponent functionals, (42)–(43)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P46

open Filter MeasureTheory QAlgorithms.RealRegisters

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Section V, PDF p.13, (42)-(43) and the preceding tilted average identity.
These evaluate actual trace and overlap-integral definitions. The coherent
overlap is credited there to Helstrom [8]. The prior is fixed Gaussian(E). -/
theorem gaussianExponentFormulas (E p : ℝ) (hE : 0 < E) (hp : 0 ≤ p) (hpE : p < 1 / E) :
    WeightedDomain (gaussian E) energyCost E p ∧
    tilted (gaussianSignal 0) (gaussian E) energyCost E p =
      (Real.exp (-p * E) / (1 - p * E) : ℂ) • constrainedCqThermal (E / (1 - p * E)) ∧
    (∀ z w : ℂ, constrainedCqOverlap (gaussianSignal 0 z) (gaussianSignal 0 w) =
      Real.exp (-Complex.normSq (z - w))) ∧
    (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      gaussianMu E s p = (1 + s) * p * E +
        Real.log ((1 + E - p * E) ^ (1 + s) - E ^ (1 + s))) ∧
    (∀ s : ℝ, 1 ≤ s →
      gaussianMuEx E s p = s * (2 * p * E +
        Real.log (1 + p ^ 2 * E ^ 2 - 2 * p * E + 2 * E * (1 - p * E) / s))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P46

end
