-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_arithmetic__p2m_24514a04_46c3_4995_8d84_ff88ef385ed2_a2
-- name    : WilliamsonShmoys.component_arithmetic__p2m_24514a04_46c3_4995_8d84_ff88ef385ed2_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:40:43.273144+00:00
-- url     : https://prove2.me/theorems/f8118d4e-7433-432b-871f-3e593ed76035
-- title:
--   Combine component edge bounds arithmetically
-- statement:
--   For a finite list of component vertex and edge counts whose totals are `n` and `E`, combine the large-component `3n − 6` bounds and small-component edge-at-most-vertex bounds to prove `E ≤ 3n − 6` when `n ≥ 3`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.component_arithmetic__p2m_24514a04_46c3_4995_8d84_ff88ef385ed2_a2
    (n E : Nat)
    (parts : List (Nat × Nat))
    (hvertices : (parts.map Prod.fst).sum = n)
    (hedges : (parts.map Prod.snd).sum = E)
    (hparts : ∀ p ∈ parts,
      (3 ≤ p.1 → p.2 ≤ 3 * p.1 - 6) ∧
      (p.1 < 3 → p.2 ≤ p.1))
    (hcard : 3 ≤ n) :
    E ≤ 3 * n - 6 := by sorry
