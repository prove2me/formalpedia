-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_randomReplacementThreshold
-- name    : QAlgorithms.Papers.Independent.Information100.P21.randomReplacementThreshold
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:04:18.727419+00:00
-- url     : https://prove2.me/theorems/263ba0a2-5fdb-4a96-9b37-129934da7886
-- title:
--   Main text — random replacement threshold
-- statement:
--   Let $\rho$ be a density operator on positive finite bipartite registers, and choose standard separable noise or generalized arbitrary density-operator noise. The least unrecorded replacement probability is
--   $$p_\nu^*=\frac{R_\nu(\rho)}{1+R_\nu(\rho)}.$$
--   The output is $(1-p)\rho+p\omega$, with noise chosen from the specified class. For every $s\ge0$, $p=s/(1+s)$ gives exactly $(\rho+s\omega)/(1+s)$. This is admixture to a specified input, not a statement about arbitrary noise dynamics.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 1, Main text — random replacement threshold

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 1, random replacement threshold. -/
theorem randomReplacementThreshold {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  (rho : Op (I × J)) (h : QAlgorithms.IsDensityMatrix rho) (standard : Bool) :
  let R := robust {X : Op (I × J) | sep X} standard rho
  IsLeast {p : ℝ | 0≤p ∧ p≤1 ∧ ∃ omega : Op (I × J),
    QAlgorithms.IsDensityMatrix omega ∧ (standard=true → sep omega) ∧
      sep ((1-p:ℂ) • rho+(p:ℂ) • omega)} (R/(1+R)) ∧
  (∀ (s : ℝ) (omega : Op (I × J)), 0 ≤ s →
    mix rho omega s=(1-s/(1+s):ℂ) • rho+(s/(1+s):ℂ) • omega) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
