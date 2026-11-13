-- Prove2me | Theorems.Thm_SigmoidWire_theorem_4_1_gamma
-- name    : SigmoidWire.theorem_4_1_gamma
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T21:04:19.176217+00:00
-- url     : https://prove2.me/theorems/3176852e-30a4-4ab4-b2af-457dbd89af50
-- title:
--   Proof of Theorem 4.1: $\mathrm{Sigmoid}^\prime\ge 1/6$ on $[0,1]$ and its mean-value form
-- statement:
--   Let $\mathrm{Sigmoid}(x)=(1+e^{-x})^{-1}$. Then:
--
--   1. $\mathrm{Sigmoid}'(\xi)\ge 1/6$ for every $\xi\in[0,1]$;
--   2. $\mathrm{Sigmoid}'(1)=e/(1+e)^2$, and this value exceeds $1/6$;
--   3. $\mathrm{Sigmoid}'$ is decreasing on $[0,\infty)$;
--   4. $\mathrm{Sigmoid}(v)-\mathrm{Sigmoid}(u)\ge\frac16(v-u)$ for all $0\le u\le v\le1$.
--
--   This gives the gap between consecutive values of the digest gate $\mathrm{Sigmoid}(|x|/n)$, which the middle layer of the depth-three circuit reads.
--
--   Differences from the source:
--   - reading: "Sigmoid′ is decreasing on [0, ∞)" → strictly decreasing on [0, ∞); reason: the stronger of the two usual readings of "decreasing", and true
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), proof of Theorem 4.1, p.18

import Mathlib

namespace SigmoidWire

/-- **Proof of Theorem 4.1, the bound `Sigmoid′ ≥ γ = 1/6` on `[0, 1]` and its mean-value form.**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), proof of Theorem 4.1, p.18
(PDF p.20): "Let γ = 1/6. We can see that Sigmoid′(ξ) ≥ γ for all ξ ∈ [0, 1], as
Sigmoid′(1) = e/(1+e)² > 1/6 and Sigmoid′ is decreasing on [0, ∞). By the mean value theorem,
Sigmoid(v) − Sigmoid(u) ≥ γ(v − u) for all 0 ≤ u ≤ v ≤ 1."

**Formalization Note.** `Sigmoid` is Mathlib's `Real.sigmoid x = (1 + e^{−x})⁻¹`; `Sigmoid′` is
`deriv Real.sigmoid`; "decreasing" is `StrictAntiOn` on `[0, ∞)`. Every clause of the sentence is a
conjunct. -/
theorem theorem_4_1_gamma :
    (∀ ξ ∈ Set.Icc (0 : ℝ) 1, (1 / 6 : ℝ) ≤ deriv Real.sigmoid ξ) ∧
    deriv Real.sigmoid 1 = Real.exp 1 / (1 + Real.exp 1) ^ 2 ∧
    (1 / 6 : ℝ) < Real.exp 1 / (1 + Real.exp 1) ^ 2 ∧
    StrictAntiOn (deriv Real.sigmoid) (Set.Ici 0) ∧
    ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ 1 →
      (1 / 6 : ℝ) * (v - u) ≤ Real.sigmoid v - Real.sigmoid u := by sorry

end SigmoidWire
