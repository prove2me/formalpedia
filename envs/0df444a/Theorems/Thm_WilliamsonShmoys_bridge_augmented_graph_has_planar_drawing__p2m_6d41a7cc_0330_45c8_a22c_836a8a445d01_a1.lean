-- Prove2me | Theorems.Thm_WilliamsonShmoys_bridge_augmented_graph_has_planar_drawing__p2m_6d41a7cc_0330_45c8_a22c_836a8a445d01_a1
-- name    : WilliamsonShmoys.bridge_augmented_graph_has_planar_drawing__p2m_6d41a7cc_0330_45c8_a22c_836a8a445d01_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:57:56.801859+00:00
-- url     : https://prove2.me/theorems/e1c10048-df1f-49a0-8080-5a203a611921
-- title:
--   The supplied noncrossing bridge gives a drawing of the augmented graph
-- statement:
--   Using the given drawing of H and the certified simple noncrossing arc c from u to v, construct a planar drawing of H with the edge uv added. The child preserves the ordered endpoint convention and proves all drawing conditions for the augmented edge set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.bridge_augmented_graph_has_planar_drawing__p2m_6d41a7cc_0330_45c8_a22c_836a8a445d01_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hEdges : ∀ a b, a < b → H.Adj a b →
      ContinuousOn (arc a b) (Set.Icc 0 1) ∧
      Set.InjOn (arc a b) (Set.Icc 0 1) ∧
      arc a b 0 = p a ∧ arc a b 1 = p b ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w)
    (hCross : ∀ a b x y, a < b → x < y → H.Adj a b → H.Adj x y →
      (a, b) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
        arc a b t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (u v : V) (c : ℝ → ℝ × ℝ)
    (huv : u < v)
    (hccont : ContinuousOn c (Set.Icc 0 1))
    (hcinj : Set.InjOn c (Set.Icc 0 1))
    (hc0 : c 0 = p u)
    (hc1 : c 1 = p v)
    (hcvertices : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, c t ≠ p w)
    (hccross : ∀ x y, x < y → H.Adj x y → (u, v) ≠ (x, y) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
        c t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :
    WilliamsonShmoys.HasPlanarDrawingOn
      (H ⊔ SimpleGraph.fromRel (fun a b => a = u ∧ b = v)) := by sorry
