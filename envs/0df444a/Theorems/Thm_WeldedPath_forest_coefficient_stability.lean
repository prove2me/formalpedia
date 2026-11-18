-- Prove2me | Theorems.Thm_WeldedPath_forest_coefficient_stability
-- name    : WeldedPath.forest_coefficient_stability
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-11-17T23:10:08.110835+00:00
-- url     : https://prove2.me/theorems/9c69ef13-6e97-460b-a45a-8d7b7fa26707
-- title:
--   Stable canonical coefficients for arbitrary recorded forests
-- statement:
--   Let H be any valid abstract forest on k vertices, G a valid welded-tree instance, n≥16 and 2≤l≤n−4. Let B contain V_bd and be disjoint from the weld. Assume
--
--   \[\frac{4k|B|}{2^n}\le\frac12,\qquad
--   \frac{192(n+1)k^3}{2^n}\le\frac12.\]
--
--   For each valid canonical description of H, form its assignment amplitude before imposing injectivity: sqrt(μ_ref(φ)) when its fixed Wfix data agree and every vertex outside its selected tree components avoids B, and zero otherwise. Let S be the complex span of these amplitudes, including all descriptions, all components and all boundary patterns.
--
--   For every f₀ in S there exists f in S such that
--
--   \[f(\phi)=f_0(\phi)\quad\text{for every injective }\phi,
--   \qquad\|f\|_2^2\le2\sum_{\phi\;\mathrm{injective}}|f_0(\phi)|^2.\]
--
--   The constant is independent of the number and sizes of connected components. This is the stable coefficient representative needed to remove noninjective assignments in the good-space analysis.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, https://arxiv.org/html/2611.05912v1#S4.SS1, Section 4.1, Lemmas 4.3-4.5. This states the coefficient-stability conclusion for the literal canonical Description span, with explicit constants and arbitrary disconnected forests.

import Definitions.Def_WeldedPath_Supplement_projGood

set_option autoImplicit false

namespace WeldedPath

open Classical Supplement
open scoped BigOperators

theorem forest_coefficient_stability :
    ∀ n l : ℕ, 16 ≤ n → 2 ≤ l → l ≤ n - 4 →
    ∀ G : WeldedInstance n, G.IsValid →
    ∀ H : AbsForest n, H.IsValid →
    ∀ B : Finset ℕ, Vbd n l ⊆ B → Disjoint B (Vweld n) →
      (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2 →
      2 * (H.k : ℝ) ^ 3 * (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) ≤ 1 / 2 →
    let amplitude := fun (sel : Finset (Fin H.k)) (φ₀ : Fin H.k → Label n) =>
      (WithLp.toLp 2 (fun φ : Fin H.k → Label n =>
        if (∀ s ∈ sel, H.Wfix φ s = H.Wfix φ₀ s) ∧
          (∀ s ∈ sel, ∀ u, H.graph.Reachable s u → u ∉ H.Ctree φ s → (φ u).val ∉ B)
        then (Real.sqrt (H.muRef l G φ) : ℂ) else 0) : Hil (Fin H.k → Label n))
    let S := Submodule.span ℂ {f | ∃ sel φ₀,
      (Description.mk H sel φ₀).IsValid ∧ f = amplitude sel φ₀}
    ∀ f₀ : Hil (Fin H.k → Label n), f₀ ∈ S →
    ∃ f : Hil (Fin H.k → Label n), f ∈ S ∧
      (∀ φ, Function.Injective φ → f φ = f₀ φ) ∧
      ‖f‖ ^ 2 ≤ 2 * ∑ φ, if Function.Injective φ then ‖f₀ φ‖ ^ 2 else 0 := by
  sorry

end WeldedPath
