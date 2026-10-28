-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P31_productInputBounds
-- name    : QAlgorithms.Papers.Independent.Support50.P31.productInputBounds
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:24:20.46626+00:00
-- url     : https://prove2.me/theorems/50eb64a0-a461-40af-92e1-c43c2a37b269
-- title:
--   Product-input norm and entropy inequalities
-- statement:
--   Let $\Phi_1,\Phi_2$ be completely positive trace-preserving endomorphisms on two nonzero finite-dimensional complex Hilbert spaces. Let $\nu_p(\Phi)$ denote the maximum output Schatten $p$-norm, with operator norm at infinity, and let $\nu_H(\Phi)$ denote minimum output von Neumann entropy in natural units. All optimizations range over density matrices. Then
--   $$
--   \nu_p(\Phi_1\otimes\Phi_2)\ge\nu_p(\Phi_1)\nu_p(\Phi_2)
--    \quad(1\le p\le\infty),\qquad
--   \nu_H(\Phi_1\otimes\Phi_2)\le\nu_H(\Phi_1)+\nu_H(\Phi_2).
--   $$
--   These inequalities compare the unrestricted joint optimization, which allows entangled inputs, with product inputs.
--
--   **Source correction.** Equation (8) prints $\Phi_1$ twice on its right side. The second occurrence is changed to $\Phi_2$, as used by the source's product-input explanation and subsequent calculation.
-- source:
--   On some additivity problems in quantum information theory, arXiv:math-ph/0003002v2, PDF p. 4, §2, equations (7)-(8): product-input inequalities

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P31

noncomputable section

open Filter Asymptotics

open scoped ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P31

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten)

open QAlgorithms.Papers.Independent.Gap48.P03 (holevoQuantity)

open QAlgorithms.Papers.Independent.Claimed50.P38 (tensorSuperop)

open QAlgorithms.Papers.Independent.Dependency50.P44 (tensorChannels)

/-- PDF p.4, (7)–(8). Printed (8) repeats Phi1; its second term is corrected
to Phi2 as required by the source's product-input argument. -/
theorem productInputBounds {I J : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J] [DecidableEq J] [Nonempty J]
    (Phi : Superop I I) (Psi : Superop J J) (hPhi : IsChannel Phi) (hPsi : IsChannel Psi) :
    (∀ p : ℝ≥0∞, 1 ≤ p → nuP p Phi * nuP p Psi ≤ nuP p (tensorSuperop Phi Psi)) ∧
      nuH (tensorSuperop Phi Psi) ≤ nuH Phi + nuH Psi := by sorry

end QAlgorithms.Papers.Independent.Support50.P31

end
