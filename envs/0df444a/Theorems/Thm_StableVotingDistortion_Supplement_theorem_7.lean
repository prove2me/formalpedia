-- Prove2me | Theorems.Thm_StableVotingDistortion_Supplement_theorem_7
-- name    : StableVotingDistortion.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:57:58.157573+00:00
-- url     : https://prove2.me/theorems/1e984cf5-8fde-4482-bbc7-4abf8b83f764
-- title:
--   Theorem 7 — $2.1232\le\inf_g\mathrm{distortion}(g)\le2.1248$ over nonconstant activations
-- statement:
--   Let $\mathrm{distortion}(g)$ be the worst-case metric distortion of a $g$-stable lottery over all elections. Then
--   $$
--   2.1232\ \le\ \inf_{g}\ \mathrm{distortion}(g)\ \le\ 2.1248,
--   $$
--   where the infimum ranges over all continuous, nondecreasing functions $g:[0,1]\to[0,1]$ that are not constant.
--
--   The lower bound says that no choice of activation pushes the distortion of $g$-stable lotteries below $2.1232$; the upper bound, which follows from Theorem 1, says that some activation comes within $0.0016$ of this.
--
--   **Formalization Note** $\mathrm{distortion}(g)$ is the least real bound valid for every $g$-stable lottery of every election, valued in the extended reals ($+\infty$ if there is none), and the infimum is taken there.
--
--   Differences from the source:
--
--   - encoding: distortion as a ratio cost_d(D)/min_a cost_d(a) → the base mission inequality HasDistortionAtMost: cost_d(D) ≤ B·cost_d(a) for every consistent pseudometric d and candidate a; reason: the base mission published convention (R3); agrees with the ratio whenever min_a cost_d(a) > 0
--   - encoding: distortion(g), the worst-case distortion of a g-stable lottery over all elections → gDistortion g : EReal, the infimum of the real bounds B with IsGDistortionBound g B (⊤ if none); reason: the supremum of the cost ratios equals the least valid bound, since valid bounds are upward closed
--   - encoding: g : [0,1] → [0,1] continuous, nondecreasing, not constant → g : ℝ → ℝ with IsActivation g (continuous and monotone on [0,1], mapping [0,1] into [0,1]) and g x ≠ g y for some x, y ∈ [0,1]; reason: the base mission convention for activations; values outside [0,1] are never used
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Theorem 7, p.21; §6, p.20

import Mathlib
import Definitions.Def_StableVotingDistortion_Supplement_gDistortion

set_option autoImplicit false

namespace StableVotingDistortion.Supplement

/-- **Theorem 7.** The optimal distortion among `g`-stable lotteries satisfies
`2.1232 ≤ inf_g distortion(g) ≤ 2.1248`, the infimum over all continuous, nondecreasing, nonconstant
`g : [0, 1] → [0, 1]`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Theorem 7, p.21: "The optimal distortion among
g-stable lotteries satisfies 2.1232 ≤ inf_g distortion(g) ≤ 2.1248, where the infimum ranges over all
continuous, nondecreasing functions g : [0, 1] → [0, 1] that are not constant"; §6, p.20: "Writing distortion(g)
for the worst-case distortion of a g-stable lottery over all elections".

**Formalization Note.** `distortion(g)` is `gDistortion g : EReal`, the least real bound valid for every
`g`-stable lottery of every election (`⊤` if none); the infimum over the class `IsNonconstantActivation` is taken
in `EReal`. No normalization of `g` is imposed on either half. -/
theorem theorem_7 :
    ((2.1232 : ℝ) : EReal) ≤ (⨅ (g : ℝ → ℝ) (_ : IsNonconstantActivation g), gDistortion g) ∧
      (⨅ (g : ℝ → ℝ) (_ : IsNonconstantActivation g), gDistortion g) ≤ ((2.1248 : ℝ) : EReal) := by sorry

end StableVotingDistortion.Supplement
