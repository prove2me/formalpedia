-- Prove2me | Theorems.Thm_TopDownParity1043_Main_lemma_11
-- name    : TopDownParity1043.Main.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T13:20:11.73921+00:00
-- url     : https://prove2.me/theorems/666c13c1-177f-44a9-a1ab-dc885b543d05
-- title:
--   Lemma 11 — variational formula for the harmonic mean
-- statement:
--   Let $A$ be the finite support of a random variable. Let $p_z>0$ be its probabilities, with $\sum_zp_z=1$, and let $g:A\to\mathbb R_{\ge0}$. Then
--   $$\left(\sum_{z\in A}p_zg_z^{-1}\right)^{-1}=\inf_{w:A\to\mathbb R_{\ge0},\ \sum_zp_zw_z=1}\sum_{z\in A}p_zg_zw_z^2.$$
--
--   The identity includes zero values of $g$ and uses $0^{-1}=+\infty$, $(+\infty)^{-1}=0$. It supplies the variational characterization used for the harmonic coefficient properties.
--
--   Differences from the source:
--   - encoding: a random variable Z with finite support → a finite type A with strictly positive weights p summing to one; reason: A indexes the support itself; every finitely supported law has exactly this representation
--   - encoding: an infimum of finite nonnegative objective values and harmonic inverses → the infimum and inverses in ℝ≥0∞; reason: the admissible set contains w ≡ 1, its objective is finite and all values are nonnegative; zeros of g retain the source inverse conventions
-- source:
--   Oliver Korten, STOC 2027 submission #1043 (October 2026), Lemma 11, p. 16

import Mathlib
import Definitions.Def_TopDownParity1043_Main_HarmonicMean

set_option autoImplicit false
open scoped NNReal ENNReal

namespace TopDownParity1043.Main

/-- Lemma 11 (Variational Formula), p.16. A indexes exactly the finite support:
its probability weights are strictly positive, while g may vanish. -/
theorem lemma_11 (A : Type) [Fintype A] (p g : A → ℝ≥0)
    (hp : ∀ z, 0 < p z) (hp1 : ∑ z, p z = 1) :
    weightedHarmonic p g =
      ⨅ (w : A → ℝ≥0) (_ : ∑ z, p z * w z = 1),
        (weightedEnergy p g w : ℝ≥0∞) := by sorry

end TopDownParity1043.Main
