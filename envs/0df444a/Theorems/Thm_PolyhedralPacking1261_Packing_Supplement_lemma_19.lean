-- Prove2me | Theorems.Thm_PolyhedralPacking1261_Packing_Supplement_lemma_19
-- name    : PolyhedralPacking1261.Packing.Supplement.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:38:24.618234+00:00
-- url     : https://prove2.me/theorems/16884b75-582b-4a7d-b130-aaa8b9a48e57
-- title:
--   Lemma 19 — under the Kakeya maximal estimate, tube unions have volume $\ge c_0 m\delta^2/\log^4(1/\delta)$
-- statement:
--   Assume the Kakeya maximal estimate (Theorem 18): there is $C_K\ge1$ with $\|K_\delta f\|_{L^3(S^2)}\le C_K\log^{4/3}(2/\delta)\|f\|_{L^3(\mathbb R^3)}$ for all $0<\delta\le1$ and $f\in L^3(\mathbb R^3)$. Then there is a constant $c_0>0$ such that for every $0<\delta\le 1/e$, every $m\ge0$, all unit vectors $v_1,\dots,v_m\in S^2$ with $\|v_i-v_j\|\ge\delta$ for $i\ne j$, and all centers $x_1,\dots,x_m\in\mathbb R^3$,
--
--   $$\mathrm{vol}\Big(\bigcup_{i=1}^m T_\delta(v_i,x_i)\Big)\ \ge\ \frac{c_0\,m\,\delta^2}{\log^4(1/\delta)}.$$
--
--   That is, the logarithmic loss $(1+\log(1/\delta))^{66}$ of the formally verified tube estimate (Theorem 17) improves to $\log^4(1/\delta)$ when the maximal estimate holds. In the paper this is the input that turns the ratio $O(\log^{69}n)$ of Theorem 2 into $O(\log^7 n)$.
--
--   Differences from the source:
--   - reading: the logarithmic factor in Theorem 17 can be replaced by log^{-4}(1/δ) → the full conclusion of Theorem 17 with c₀mδ²/log⁴(1/δ): ∃ c₀ > 0 before δ ∈ (0, 1/e], m, unit directions with Euclidean separation ≥ δ, and arbitrary centers; reason: the lemma states the replacement in words; this is the statement it produces, keeping every quantifier of Theorem 17
--   - encoding: If Theorem 18 holds (K_δ f, L³(S²) with surface measure, f ∈ L³(ℝ³)) → hypothesis KakeyaMaximalEstimate: [0,∞]-valued supremum and lower Lebesgue integrals, Mathlib's toSphere surface-area measure (total mass 4π), f with MemLp f 3; reason: the same assertion; the integrand is a supremum of continuous averages, hence measurable, so the lower integral is the integral
--   - encoding: S², vol, 1/e → unit vectors of EuclideanSpace ℝ (Fin 3), Lebesgue measure in [0,∞], Real.exp (-1); reason: Lean conventions; same instances
-- source:
--   Simon Bartlmae, Anders Aamand, Mikkel Abrahamsen, Polylogarithmic Approximation for Packing Convex Polyhedra, STOC 2027 submission #1261 (October 2026), canonical PDF SHA-256 b915da2d5fece730ea9946885b05ad09e10e575374e6a1df96e8a6149cb0e67e, Lemma 19 and its proof, Appendix B.1, PDF p.27 (printed p.26); Theorems 17 and 18, PDF pp.26–27 (printed pp.25–26)

import Definitions.Def_PolyhedralPacking1261_Packing_Supplement_Kakeya

set_option autoImplicit false

open MeasureTheory

namespace PolyhedralPacking1261.Packing.Supplement

/-- Lemma 19, PDF p.27 (printed p.26). If the Kakeya maximal estimate (Theorem 18)
holds, then the tube-union bound of Theorem 17 holds with the factor
`(1 + log(1/δ))^{-66}` replaced by `log^{-4}(1/δ)`: one constant `c₀ > 0` serves every
`0 < δ ≤ 1/e`, every finite family of unit directions at pairwise Euclidean distance
at least `δ`, and every choice of centers. -/
theorem lemma_19 (hK : KakeyaMaximalEstimate) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ Real.exp (-1) →
      ∀ (m : ℕ) (v : Fin m → E3), (∀ i, ‖v i‖ = 1) →
        (∀ i j, i ≠ j → δ ≤ ‖v i - v j‖) → ∀ x : Fin m → E3,
          ENNReal.ofReal (c₀ * (m : ℝ) * δ ^ 2 / Real.log (1 / δ) ^ 4) ≤
            volume (⋃ i, tube δ (v i) (x i)) := by sorry

end PolyhedralPacking1261.Packing.Supplement
