-- Prove2me | Theorems.Thm_WeldedPath_connected_coefficient_stability
-- name    : WeldedPath.connected_coefficient_stability
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-11-17T22:14:49.804053+00:00
-- url     : https://prove2.me/theorems/e79476de-9d05-4294-a815-993763250b13
-- title:
--   Stable coefficients for connected forests across all boundary patterns
-- statement:
--   Let H be a valid connected abstract forest on k vertices and G a valid welded-tree instance, with n≥16 and 2≤l≤n−4. Let B contain V_bd and be disjoint from V_weld. Assume
--
--   \[
--   \frac{4k|B|}{2^n}\le\frac12,
--   \qquad
--   \frac{96(n+1)k^3}{2^n}\le\frac12.
--   \]
--
--   For an arbitrary complex coefficient family h(F,v,d), define its represented amplitude by
--
--   \[
--   \psi_h(\phi)=\sqrt{\mu^{\rm ref}(\phi)}
--   \sum_{F\subseteq [k]}\sum_{v\in[k]}
--   \mathbf 1_{\{F=\{u:\phi(u)\in B\},\;F\subseteq C^{\rm tree}_\phi(v)\}}
--   h(F,v,W^{\rm fix}_\phi(v)).
--   \]
--
--   There exists another coefficient family h′ such that ψ_h′(φ)=ψ_h(φ) for every injective assignment φ, and
--
--   \[
--   \|\psi_{h'}\|_2^2\le
--   2\sum_{\phi\text{ injective}}|\psi_h(\phi)|^2.
--   \]
--
--   The conclusion concerns the norm of the represented amplitude. It covers the empty boundary pattern and every nonempty boundary pattern, without a factor counting the number of patterns.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, https://arxiv.org/html/2611.05912v1#S4.SS1, Section 4.1 and the coefficient-stability step of Lemma 4.3. This is an explicit connected-forest intermediate with the canonical reference measure and fixed data, covering all exact boundary-label patterns.

import Definitions.Def_WeldedPath_Supplement_projGood

namespace WeldedPath

open Classical Supplement
open scoped BigOperators

theorem connected_coefficient_stability :
    ∀ n l : ℕ, 16 ≤ n → 2 ≤ l → l ≤ n - 4 →
    ∀ G : WeldedInstance n, G.IsValid →
    ∀ H : AbsForest n, H.IsValid →
    ∀ s : Fin H.k, (∀ u, H.graph.Reachable s u) →
    ∀ B : Finset ℕ, Vbd n l ⊆ B → Disjoint B (Vweld n) →
      (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2 →
      (H.k : ℝ) ^ 3 * (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) ≤ 1 / 2 →
    ∀ h : Finset (Fin H.k) → Fin H.k →
      (Finset (Fin H.k) × Finset (Fin H.k × ℕ) × Finset (Fin H.k × ℕ)) → ℂ,
    let amplitude := fun h : Finset (Fin H.k) → Fin H.k →
      (Finset (Fin H.k) × Finset (Fin H.k × ℕ) × Finset (Fin H.k × ℕ)) → ℂ =>
      (WithLp.toLp 2 (fun φ : Fin H.k → Label n =>
        ∑ F : Finset (Fin H.k), ∑ v : Fin H.k,
          if (∀ u, (φ u).val ∈ B ↔ u ∈ F) ∧ F ⊆ H.Ctree φ v then
            (Real.sqrt (H.muRef l G φ) : ℂ) * h F v (H.Wfix φ v) else 0) :
        Hil (Fin H.k → Label n))
    ∃ h',
      (∀ φ, Function.Injective φ → amplitude h' φ = amplitude h φ) ∧
      ‖amplitude h'‖ ^ 2 ≤
        2 * ∑ φ, if Function.Injective φ then ‖amplitude h φ‖ ^ 2 else 0 := by
  sorry

end WeldedPath
