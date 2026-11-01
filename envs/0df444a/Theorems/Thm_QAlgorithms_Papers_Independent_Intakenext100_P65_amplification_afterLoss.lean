-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P65_amplification_afterLoss
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P65.amplification_afterLoss
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:36:08.190433+00:00
-- url     : https://prove2.me/theorems/2c4b5d91-bd0c-4a70-a26e-aa6abc5be835
-- title:
--   Amplification after pure loss equals Gaussian displacement noise
-- statement:
--   Let $0<\gamma<1$ and let $\rho$ be any positive trace-one operator on the complete oscillator Hilbert space. Write $\mathcal N_\gamma(\rho)=\sum_{\ell\ge0}E_\ell\rho E_\ell^\dagger$, and construct the quantum-limited amplifier with Kraus operators $\sqrt{1-\gamma}E_\ell^\dagger$. The resulting amplification-after-loss output is a positive trace-one operator, and each of its number-basis entries is given by an integrable displacement average:
--
--   $$\mathcal A\mathcal N_\gamma(\rho)=\frac{1-\gamma}{\pi\gamma}\int_{\mathbb C}e^{-(1-\gamma)|\alpha|^2/\gamma}D_\alpha\rho D_\alpha^\dagger\,d^2\alpha.$$
--
--   The added displacement variance is $\gamma/(1-\gamma)$. Positivity is encoded by all finite principal compressions and the nonnegative summable diagonal has trace one; this characterizes positive trace-class kernels and imposes no cutoff. No Schrödinger channel is applied to the identity.
-- source:
--   Performance and structure of single-mode bosonic codes, arXiv:1708.05010v3, PDF p. 20, §VII B (7.20)–(7.21): amplification after loss

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P65

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P65

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Frontier18.P14 (displacementEntry)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open scoped ComplexConjugate Matrix Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.20 (7.21): exact composition, amplification AFTER loss, with the source
variance g/(1-g); full positive trace-class inputs, not the non-trace-class identity. -/
theorem amplification_afterLoss (g : ℝ) (hg0 : 0 < g) (hg1 : g < 1)
    (R : ℕ → ℕ → ℂ) (hR : fockDensity R) :
    fockDensity (amplifierChannel g (lossChannel g R)) ∧
    (∀ n m : ℕ, Integrable (fun z : ℂ => (amplifiedLossDensity g z : ℂ) * displaceDensity z R n m) ∧
      amplifierChannel g (lossChannel g R) n m =
        ∫ z : ℂ, (amplifiedLossDensity g z : ℂ) * displaceDensity z R n m) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P65

end
