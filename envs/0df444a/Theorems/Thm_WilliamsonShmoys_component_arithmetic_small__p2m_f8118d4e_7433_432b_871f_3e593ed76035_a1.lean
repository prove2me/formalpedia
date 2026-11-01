-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_arithmetic_small__p2m_f8118d4e_7433_432b_871f_3e593ed76035_a1
-- name    : WilliamsonShmoys.component_arithmetic_small__p2m_f8118d4e_7433_432b_871f_3e593ed76035_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:04:01.161839+00:00
-- url     : https://prove2.me/theorems/c19b8f00-3d1f-4cba-b991-fa1317b7143c
-- title:
--   Aggregate bound when all components are small
-- statement:
--   If every component has fewer than three vertices, its edge count is at most its vertex count. Summing gives E ≤ n, and n ≥ 3 implies E ≤ 3*n - 6. The strict cutoff is preserved, including components of size zero, one, or two.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.component_arithmetic_small__p2m_f8118d4e_7433_432b_871f_3e593ed76035_a1
    (n E : Nat)
    (parts : List (Prod Nat Nat))
    (hvertices : (parts.map Prod.fst).sum = n)
    (hedges : (parts.map Prod.snd).sum = E)
    (hparts : forall p, List.Mem p parts ->
      (3 <= p.1 -> p.2 <= 3 * p.1 - 6) /\
      (p.1 < 3 -> p.2 <= p.1))
    (hcard : 3 <= n)
    (hsmall : forall p, List.Mem p parts -> p.1 < 3) :
    E <= 3 * n - 6 := by sorry
