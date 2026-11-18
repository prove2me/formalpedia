-- Prove2me | Theorems.Thm_WeldedPath_reference_conditional_bounds
-- name    : WeldedPath.reference_conditional_bounds
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-11-17T21:34:24.399174+00:00
-- url     : https://prove2.me/theorems/9086c803-4b7b-44aa-9394-7a3fa0213330
-- title:
--   Conditional concentration and collision bounds for a connected reference forest
-- statement:
--   Let G be a valid welded-tree instance with n >= 16 and 2 <= l <= n-4. Let H be a valid connected abstract forest, with a chosen vertex s, and let phi_0 be a reference labeling with nonzero reference weight muRef. Let B contain V_bd and be disjoint from the weld, and suppose 4 |V(H)| |B| / 2^n <= 1/2. Weight labelings phi by muRef(phi), restrict to Wfix(phi,s)=Wfix(phi_0,s), and exclude labels in B at vertices outside Ctree(phi,s). Normalize this restricted finite measure. Every vertex outside Sfix(phi_0,s) has probability at most 8/2^n of receiving any prescribed label. Any two distinct vertices outside Sfix(phi_0,s) have probability at most 96(n+1)/2^n of receiving the same label.
--
--   The formal statement expresses each conditional probability as a quotient of finite weighted sums. It concerns the reference measure before imposing injectivity. The two displayed constants are explicit derived bounds. The result is the connected-component conditional concentration ingredient of Lemma 4.3, using the literal canonical Wfix, Ctree, Sfix, and muRef definitions.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, https://arxiv.org/html/2611.05912v1#S4.SS1, Section 4.1, reference measure (50) and conditional point/collision estimates in Lemma 4.3. Constants 8 and 96 are proved explicitly in this formalization; this statement isolates the connected-component case.

import Definitions.Def_WeldedPath_Supplement_projGood

set_option autoImplicit false

namespace WeldedPath

open Classical Supplement
open scoped BigOperators

theorem reference_conditional_bounds :
    ∀ n l : ℕ, 16 ≤ n → 2 ≤ l → l ≤ n - 4 →
    ∀ G : WeldedInstance n, G.IsValid →
    ∀ H : AbsForest n, H.IsValid →
    ∀ (φ₀ : Fin H.k → Label n) (s : Fin H.k),
      (∀ u, H.graph.Reachable s u) → H.muRef l G φ₀ ≠ 0 →
    ∀ B : Finset ℕ, Vbd n l ⊆ B → Disjoint B (Vweld n) →
      (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2 →
    let weight : (Fin H.k → Label n) → ℝ := fun φ =>
      if H.Wfix φ s = H.Wfix φ₀ s ∧
          (∀ u, H.graph.Reachable s u → u ∉ H.Ctree φ s → (φ u).1 ∉ B)
      then H.muRef l G φ else 0
    (∀ (u : Fin H.k), u ∉ H.Sfix φ₀ s → ∀ x : Label n,
      (∑ φ, if φ u = x then weight φ else 0) / (∑ φ, weight φ) ≤
        8 / (2 : ℝ) ^ n) ∧
    (∀ (u v : Fin H.k), u ∉ H.Sfix φ₀ s → v ∉ H.Sfix φ₀ s → u ≠ v →
      (∑ φ, if φ u = φ v then weight φ else 0) / (∑ φ, weight φ) ≤
        96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) := by
  sorry

end WeldedPath
