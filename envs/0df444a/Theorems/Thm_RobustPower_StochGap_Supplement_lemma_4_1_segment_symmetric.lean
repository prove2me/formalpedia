-- Prove2me | Theorems.Thm_RobustPower_StochGap_Supplement_lemma_4_1_segment_symmetric
-- name    : RobustPower.StochGap.Supplement.lemma_4_1_segment_symmetric
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:33:40.498967+00:00
-- url     : https://prove2.me/theorems/084730d3-dbb8-4c7b-bc64-34589bd5a87b
-- title:
--   Lemma 4.1, p. 25 — the segment {b ≥ 0 : b₁ + b₂ = 1} is symmetric about (1/2, 1/2)
-- statement:
--   Let
--   $$I(\Omega)=\{b\in\mathbb R^2_+ : b_1+b_2=1\}.$$
--   Then $I(\Omega)$ is symmetric (Definition 1.2) with centre $u^0=(\tfrac12,\tfrac12)$: $u^0\in I(\Omega)$ and, for every $z\in\mathbb R^2$, $u^0+z\in I(\Omega)$ if and only if $u^0-z\in I(\Omega)$.
--
--   This is the symmetry hypothesis that makes the instance of Theorem 4.3 a tight example for Theorem 4.1.
--
--   **Formalization Note** Coordinates are indexed by `Fin 2`, so $b_1,b_2$ are `v 0`, `v 1`. Symmetry is the published `IsSymmetricAbout`, which includes membership of the centre.
--
--   Differences from the source:
--
--   - encoding: coordinates b₁, b₂ → v 0, v 1 of v : Fin 2 → ℝ; reason: 0-based indexing; same set
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 25, Lemma 4.1 and its proof

import Mathlib
import Definitions.Def_RobustPower_StochGap_SymmetricSets

namespace RobustPower.StochGap.Supplement

/-- Lemma 4.1 (p. 25): the segment `{b ∈ ℝ²₊ | b₁ + b₂ = 1}` is symmetric (Definition 1.2)
with centre `u⁰ = (1/2, 1/2)`. -/
theorem lemma_4_1_segment_symmetric :
    RobustPower.StochGap.IsSymmetricAbout {v : Fin 2 → ℝ | 0 ≤ v ∧ v 0 + v 1 = 1}
      (fun _ => (1 / 2 : ℝ)) := by sorry

end RobustPower.StochGap.Supplement
