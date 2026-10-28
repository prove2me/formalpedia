-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P31_normMultiplicativityImpliesEntropyAdditivity
-- name    : QAlgorithms.Papers.Independent.Support50.P31.normMultiplicativityImpliesEntropyAdditivity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:26:08.109631+00:00
-- url     : https://prove2.me/theorems/43d8b713-69fb-44d9-a9e7-3a0fe505d9c7
-- title:
--   Multiplicativity arbitrarily near one implies entropy additivity
-- statement:
--   Let $\Phi_1,\Phi_2$ be completely positive trace-preserving endomorphisms on nonzero finite-dimensional complex Hilbert spaces. For each channel let $\nu_p$ be maximum output Schatten $p$-norm and $\nu_H$ minimum output entropy in natural units, with all density inputs allowed. Assume that for every $\delta>0$ there is a real exponent $p$ satisfying
--   $$
--   1<p<1+\delta,\qquad
--   \nu_p(\Phi_1\otimes\Phi_2)=\nu_p(\Phi_1)\nu_p(\Phi_2).
--   $$
--   Then
--   $$
--   \nu_H(\Phi_1\otimes\Phi_2)=\nu_H(\Phi_1)+\nu_H(\Phi_2).
--   $$
--   Only equality at exponents arbitrarily close to one is required; the hypothesis does not demand an entire interval of multiplicativity.
-- source:
--   On some additivity problems in quantum information theory, arXiv:math-ph/0003002v2, PDF p. 4, §2, unnumbered implication following (8)

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

/-- PDF p.4: equality in (7) arbitrarily close to 1 from above suffices.
No interval of equality is assumed; equality at 1 alone has no content. -/
theorem normMultiplicativityImpliesEntropyAdditivity {I J : Type}
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J] [Nonempty J]
    (Phi : Superop I I) (Psi : Superop J J) (hPhi : IsChannel Phi) (hPsi : IsChannel Psi)
    (hmul : ∀ delta : ℝ, 0 < delta → ∃ p : ℝ, 1 < p ∧ p < 1 + delta ∧
      nuP (ENNReal.ofReal p) (tensorSuperop Phi Psi) =
        nuP (ENNReal.ofReal p) Phi * nuP (ENNReal.ofReal p) Psi) :
    nuH (tensorSuperop Phi Psi) = nuH Phi + nuH Psi := by sorry

end QAlgorithms.Papers.Independent.Support50.P31

end
