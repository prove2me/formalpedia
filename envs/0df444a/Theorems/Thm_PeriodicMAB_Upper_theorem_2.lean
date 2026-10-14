-- Prove2me | Theorems.Thm_PeriodicMAB_Upper_theorem_2
-- name    : PeriodicMAB.Upper.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:00.578568+00:00
-- url     : https://prove2.me/theorems/b979844f-3eb9-4d0c-8a81-b996bc855d1d
-- title:
--   Theorem 2, p. 20 — Algorithm 1 identifies all periods with probability $\ge1-48K/n^{H^2-1}-200K/n^{0.867H^2-1}-200K/n^{0.6934H^2-1}$
-- statement:
--   Let the noise satisfy Assumption 2 with parameter $\sigma>0$, let every arm have a mean sequence of minimum period $T_k$, let $H>0$, and assume Assumptions 3 and 4. Let $\Lambda=\{\hat T_k=T_k\ \forall k\}$ be the event that Algorithm 1 estimates every period correctly. Then
--   $$
--   \mathbb P(\Lambda)\ge1-\frac{48K}{n^{H^2-1}}-\frac{200K}{n^{0.867H^2-1}}-\frac{200K}{n^{0.6934H^2-1}} .
--   $$
--
--   This is the guarantee of stage one; on $\Lambda$ the two-stage policy coincides with the weak oracle.
--
--   **Formalization Note** The paper prints $0.694$ in the last exponent; the proof supports $0.6934$ (see Lemma 7). Assumption 1 is not assumed, as printed ("Under Assumption 2 – 4"). Stated as $\mathbb P(\Lambda^c)\le\dots$ (outer measure). Algorithm 1 is as defined in `PeriodicMAB.Upper.Spectral`, with its canonical tie-breaking and the bound of $n$ loop passes.
-- source:
--   Chen, Wang and Wang, Learning and Optimization with Seasonal Patterns, arXiv:2005.08088v4, p. 20, Theorem 2

import Mathlib
import Definitions.Def_PeriodicMAB_Upper_Model
import Definitions.Def_PeriodicMAB_Upper_Spectral

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace PeriodicMAB.Upper

/-- Theorem 2 (p. 20), with the exponent `0.6934` that the proof establishes in place of the
printed `0.694`: under Assumptions 2–4, Algorithm 1 identifies every period with probability
`P(Λ) ≥ 1 − 48K/n^{H²−1} − 200K/n^{0.867H²−1} − 200K/n^{0.6934H²−1}`. -/
theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ) (σ : ℝ≥0) (hσ : 0 < σ) (hε : IsSubGaussianNoise P ε σ)
    {K : ℕ} (μ : Fin K → ℕ → ℝ) (Tper : Fin K → ℕ) (T n g : ℕ) (H : ℝ) (hH : 0 < H)
    (hper : ∀ k, IsMinPeriod (μ k) (Tper k)) (hA3 : Assumption3 T n g Tper)
    (hA4 : Assumption4 μ Tper σ H n g) :
    P (eventLambda μ ε σ H n g Tper)ᶜ ≤
      ENNReal.ofReal (48 * K / (n : ℝ) ^ (H ^ 2 - 1) + 200 * K / (n : ℝ) ^ (0.867 * H ^ 2 - 1) +
        200 * K / (n : ℝ) ^ (0.6934 * H ^ 2 - 1)) := by sorry

end PeriodicMAB.Upper
