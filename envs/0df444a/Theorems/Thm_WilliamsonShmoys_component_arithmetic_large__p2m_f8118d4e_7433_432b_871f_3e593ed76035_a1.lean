-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_arithmetic_large__p2m_f8118d4e_7433_432b_871f_3e593ed76035_a1
-- name    : WilliamsonShmoys.component_arithmetic_large__p2m_f8118d4e_7433_432b_871f_3e593ed76035_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:04:00.947678+00:00
-- url     : https://prove2.me/theorems/07bb27f9-889c-495f-953a-66659928e1ba
-- title:
--   Aggregate bound when a large component exists
-- statement:
--   If one component has at least three vertices, and every component satisfies the corresponding large or small edge bound, then the total edge count is at most three times the total vertex count minus six. The witness supplies the six-unit deficit; other components need only satisfy the bound by three times their vertex count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.component_arithmetic_large__p2m_f8118d4e_7433_432b_871f_3e593ed76035_a1
    (n E : Nat)
    (parts : List (Prod Nat Nat))
    (hvertices : (parts.map Prod.fst).sum = n)
    (hedges : (parts.map Prod.snd).sum = E)
    (hparts : forall p, List.Mem p parts ->
      (3 <= p.1 -> p.2 <= 3 * p.1 - 6) /\
      (p.1 < 3 -> p.2 <= p.1))
    (hlarge : Exists (fun p => And (List.Mem p parts) (3 <= p.1))) :
    E <= 3 * n - 6 := by sorry
