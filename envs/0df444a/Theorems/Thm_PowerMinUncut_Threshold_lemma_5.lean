-- Prove2me | Theorems.Thm_PowerMinUncut_Threshold_lemma_5
-- name    : PowerMinUncut.Threshold.lemma_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:44:45.838275+00:00
-- url     : https://prove2.me/theorems/f51c9f99-7cf3-4b6f-a3f4-6a56cab2d4aa
-- title:
--   Lemma 5 — topological volume: an odd W^{1,q} map S^q → S^{k−1} has total q-Jacobian at least |S^q|
-- statement:
--   Let $q\ge2$ be an integer. Every odd $F\in W^{1,q}(S^q;S^{k-1})$ satisfies
--   $$\int_{S^q}J_q(D_SF)\,d\,\mathrm{area}\ge|S^q|,$$
--   where $D_SF$ is the tangential weak derivative, $J_q$ its $q$-Jacobian on the tangent space, and $|S^q|$ the surface area of the unit sphere $S^q\subset\mathbb R^{q+1}$.
--
--   The bound expresses that odd maps have odd degree after a Gaussian projection to $S^q$; it is the topological input of the directional-energy inequality.
--
--   Differences from the source:
--   - encoding: W^{1,q}(S^q; S^{k−1}), odd → `IsOddSphereSobolev`: F, G ∈ L^q(σ), G(x)x = 0, weak derivative along every rotation field V_ab; ‖F‖ = 1 and F(−x) = −F(x) σ-a.e.; reason: the rotation fields preserve σ and span every tangent space, so this is W^{1,q} with D_S F = G
--   - encoding: J_q(D_S F) → √det(GᵀG + xxᵀ); reason: equals the Gram determinant of G(x) on an orthonormal basis of T_xS^q because G(x)x = 0
-- source:
--   Xie, Sharp Power Loss Thresholds for Vector Min Uncut, STOC 2027 submission (manuscript sha256 391063da…), p. 6, §2.2, Lemma 5

import Mathlib
import Definitions.Def_PowerMinUncut_Threshold_Sobolev

open MeasureTheory ProbabilityTheory Filter Topology

namespace PowerMinUncut.Threshold

/-- **Lemma 5**, p. 6. For an integer `q ≥ 2`, every odd `F ∈ W^{1,q}(S^q; S^{k-1})` satisfies
`∫_{S^q} J_q(D_S F) d area ≥ |S^q|` (unnormalized surface measure). -/
theorem lemma_5 (q k : ℕ) (hq : 2 ≤ q) (F : E (q + 1) → E k)
    (DF : E (q + 1) → (E (q + 1) →L[ℝ] E k)) (hF : IsOddSphereSobolev q q F DF) :
    (sphereArea q Set.univ).toReal ≤
      ∫ x : Metric.sphere (0 : E (q + 1)) 1, sphereJac (DF x) (x : E (q + 1)) ∂sphereArea q := by sorry

end PowerMinUncut.Threshold
