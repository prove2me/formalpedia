-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P85_coherent_mode_concentration
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P85.coherent_mode_concentration
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:22:22.400876+00:00
-- url     : https://prove2.me/theorems/1d51c259-fa29-4aca-889d-a996ce79d373
-- title:
--   p.4: coherent product concentrates into one collective mode
-- statement:
--   Let $M\ge1$ and $N_S\ge0$. On the full $M$-mode oscillator space, there exist a real orthogonal matrix $O$ whose first row is $(1/\sqrt M,\ldots,1/\sqrt M)$ and a passive unitary $U$ acting on every coherent vector by $U|\alpha\rangle=|O\alpha\rangle$. In particular,
--   $$
--   U\bigotimes_{m=1}^M|\sqrt{N_S}\rangle_m
--   =|\sqrt{MN_S}\rangle_1\otimes\bigotimes_{m=2}^M|0\rangle_m.
--   $$
--   The coherent vectors have their full number coefficients and unit norm. The action on all coherent amplitudes fixes the unitary's vacuum phase. This expresses concentration in an actual changed mode basis; $M=1$ gives the original mode and $N_S=0$ gives vacuum throughout.
-- source:
--   Quantum Illumination with Gaussian States, arXiv:0810.0534v1, PDF p. 4, p.4: coherent product concentrates into one collective mode

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P85

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakenext100.P85

open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)

open QAlgorithms.Papers.Independent.Renew46.P41 (coherentProductCoefficient)

/-- Source p.4, concluding coherent-mode observation. An orthogonal mode
basis change with normalized uniform first row has an actual passive unitary
on the full oscillator Hilbert space. Its action is pinned on every coherent
vector, fixing also its vacuum/global phase convention. -/
theorem coherent_mode_concentration (M : ℕ) (hM : 0 < M) (NS : ℝ) (hNS : 0 ≤ NS) :
    (∀ alpha : Fin M → ℂ,
      (∀ j, coherentVector alpha j = coherentProductCoefficient alpha j) ∧
      ‖coherentVector alpha‖ = 1) ∧
    ∃ (O : Matrix (Fin M) (Fin M) ℝ)
      (U : G.ModeHilbert M ≃ₗᵢ[ℂ] G.ModeHilbert M),
      O * O.transpose = 1 ∧
      (∀ r : Fin M, O ⟨0, hM⟩ r = (Real.sqrt (M : ℝ))⁻¹) ∧
      (∀ alpha : Fin M → ℂ, U (coherentVector alpha) =
        coherentVector (fun r => ∑ s, (O r s : ℂ) * alpha s)) ∧
      U (coherentVector (constantAmplitude M NS)) =
        coherentVector (fun r => if r.val = 0 then (Real.sqrt ((M : ℝ) * NS) : ℂ) else 0) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P85

end
