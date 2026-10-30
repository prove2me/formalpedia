-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P36_coherentAntipodalInner
-- name    : QAlgorithms.Papers.Independent.Advance50.P36.coherentAntipodalInner
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T13:53:02.973008+00:00
-- url     : https://prove2.me/theorems/46a928df-6b72-4a58-b7fb-31845f156330
-- title:
--   Exact antipodal coherent-state inner product
-- statement:
--   For every finite complex amplitude $\alpha$, let $|\alpha\rangle$ be the canonical oscillator coherent vector with number-basis coefficient $e^{-|\alpha|^2/2}\alpha^n/\sqrt{n!}$ at occupation $n\in\mathbb N$. Both $|\alpha\rangle$ and $|-\alpha\rangle$ are normalized, and their exact complex inner product is
--   $$
--   \langle\alpha|-\alpha\rangle=e^{-2|\alpha|^2}.
--   $$
--   The right-hand side is a positive real number embedded in $\mathbb C$. The identity includes $\alpha=0$, where it reads $1=1$, and supplies the overlap entering the coherent reading benchmark.
--
--   **Formalization Note** This is an identity of actual full-Fock inner products, with coefficient realization concluded; it is not merely a scalar kernel definition or a squared-modulus identity.
-- source:
--   Error free Quantum Reading by Quasi Bell State of Entangled Coherent States, arXiv:1108.4163v2, PDF p. 3, §IV, Eq.(13)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P36

open QAlgorithms.Papers.Independent.Frontier30.P21
  (WordFock coherentWord CoherentWordRealized binaryErrorValues)

open scoped Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.3, Eq.(13): exact complex antipodal overlap for actual one-mode
coherent vectors, including alpha=0. Coefficients and unit norms are concluded,
so the scalar kernel is not substituted for an unproved Hilbert identity. -/
theorem coherentAntipodalInner (alpha : ℂ) :
    CoherentWordRealized ![alpha] ∧ CoherentWordRealized ![-alpha] ∧
    inner (𝕜 := ℂ) (coherentWord ![alpha]) (coherentWord ![-alpha]) =
      (Real.exp (-2 * Complex.normSq alpha) : ℂ) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P36

end
