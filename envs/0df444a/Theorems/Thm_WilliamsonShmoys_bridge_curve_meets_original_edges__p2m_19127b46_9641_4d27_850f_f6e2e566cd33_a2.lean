-- Prove2me | Theorems.Thm_WilliamsonShmoys_bridge_curve_meets_original_edges__p2m_19127b46_9641_4d27_850f_f6e2e566cd33_a2
-- name    : WilliamsonShmoys.bridge_curve_meets_original_edges__p2m_19127b46_9641_4d27_850f_f6e2e566cd33_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:41:29.47572+00:00
-- url     : https://prove2.me/theorems/ebffb4a8-0bdd-4f51-a01d-c33571a48d1a
-- title:
--   Transfer augmented drawing crossings to original edges
-- statement:
--   Show that the extracted bridge curve meets every original edge arc only at endpoints. The source is the augmented drawing's crossing condition. For an original G-edge, hrel supplies H adjacency; hrel also supplies adjacency of the added pair. If their sorted endpoint pairs were equal, the original edge would connect x and y, contradicting hxy (using symmetry if the order is reversed). Apply hcross to the distinct sorted pairs. In the reverse bridge orientation, translate the crossing parameter through 1 - t; this maps interval endpoints to endpoints. This removes the edge-by-edge crossing transfer from the parent. Its remaining core is establishing distinctness of the unordered endpoint pairs and translating endpoint equalities under parameter reversal.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.bridge_curve_meets_original_edges__p2m_19127b46_9641_4d27_850f_f6e2e566cd33_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (x y : V)
    (hxy : ¬ G.Reachable x y)
    (hrel : ∀ u v, H.Adj u v ↔
      G.Adj u v ∨ (u = x ∧ v = y) ∨ (u = y ∧ v = x))
    (arc : V → V → ℝ → ℝ × ℝ)
    (hcross : ∀ u v a b, u < v → a < b → H.Adj u v → H.Adj a b →
      (u, v) ≠ (a, b) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        arc u v t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (γ : ℝ → ℝ × ℝ)
    (hrep : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ t = if x < y then arc x y t else arc y x (1 - t)) :
    ∀ u v, u < v → G.Adj u v →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        γ t = arc u v s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1) := by sorry
