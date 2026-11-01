-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P65_lossProduct_displacementIntegral
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P65.lossProduct_displacementIntegral
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:35:09.203644+00:00
-- url     : https://prove2.me/theorems/8bf63934-7b23-4b8e-9b94-3a0d9c0ff3fb
-- title:
--   Exact displacement expansion of loss-error products
-- statement:
--   Let $0<\gamma<1$ and $\ell,k,n,m\ge0$ be integers. The full-Fock pure-loss Kraus operator obeys $E_\ell|j\rangle=\sqrt{\binom j\ell}\gamma^{\ell/2}(1-\gamma)^{(j-\ell)/2}|j-\ell\rangle$ for $j\ge\ell$, and is zero otherwise. Use $D_\alpha=e^{\alpha\hat a^\dagger-\alpha^*\hat a}$. Then the following integral is absolutely integrable and gives every number-basis entry of the product:
--
--   $$\langle n|E_\ell^\dagger E_k|m\rangle=\int_{\mathbb C}\frac{d^2\alpha}{\pi}\,e^{-(1-\gamma)|\alpha|^2/2}\langle\ell|D_{\alpha^*}|k\rangle\langle n|D_{\sqrt\gamma\alpha}|m\rangle.$$
--
--   Displacement matrix elements are constructed by the finite normal-ordering formula. The trace expansion excludes $\gamma=0$, where trace-class damping is lost.
-- source:
--   Performance and structure of single-mode bosonic codes, arXiv:1708.05010v3, PDF p. 19, §VII A (7.12): exact displacement integral of loss-error products

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P65

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P65

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Frontier18.P14 (displacementEntry)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open scoped ComplexConjugate Matrix Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.19 (7.12): exact weak operator identity, expressed on every pair of
number states; integrability prevents a default-valued Bochner integral. -/
theorem lossProduct_displacementIntegral (g : ℝ) (hg0 : 0 < g) (hg1 : g < 1)
    (l k n m : ℕ) :
    Integrable (lossDisplacementIntegrand g l k n m) ∧
    lossProduct g l k n m = ∫ z : ℂ, lossDisplacementIntegrand g l k n m z := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P65

end
