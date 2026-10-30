-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_edgeFinset_card_le_three_mul_card_sub_six__p2m_16e02065_aa02_4917_a9e7_1c4778a9d41f_a1
-- name    : WilliamsonShmoys.drawable_edgeFinset_card_le_three_mul_card_sub_six__p2m_16e02065_aa02_4917_a9e7_1c4778a9d41f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:53:13.251385+00:00
-- url     : https://prove2.me/theorems/270023aa-f627-4b53-97e3-8e37f4bb2eb9
-- title:
--   Planar drawing edge-count upper bound
-- statement:
--   Every finite simple graph with the supplied crossing-free drawing and at least three vertices has at most 3n−6 edges. This isolates the Euler-formula upper-bound argument, which does not use maximality. A proof route is to obtain the embedding's face structure, apply Euler's formula componentwise or after connecting components in the outer face, and use that every face boundary has length at least three, with the small boundary cases handled using simplicity and n ≥ 3.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_edgeFinset_card_le_three_mul_card_sub_six__p2m_16e02065_aa02_4917_a9e7_1c4778a9d41f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    M.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
