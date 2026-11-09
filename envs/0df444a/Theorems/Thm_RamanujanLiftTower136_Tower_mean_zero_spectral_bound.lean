-- Prove2me | Theorems.Thm_RamanujanLiftTower136_Tower_mean_zero_spectral_bound
-- name    : RamanujanLiftTower136.Tower.mean_zero_spectral_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:39:47.794213+00:00
-- url     : https://prove2.me/theorems/dd89eef5-00d4-4518-bb66-425709241e88
-- title:
--   Proposition 5.1 — mean-zero spectral bound
-- statement:
--   For every prime $p\equiv1\pmod{17}$ and every $n\ge1$, let $h:\mathbb Z/2^n\mathbb Z\to\mathbb C$ be a nonzero function with $\sum_t h(t)=0$. If $\lambda\in\mathbb C$ satisfies $A_{n,p}h=\lambda h$, then
--   $$|\lambda|\le2\sqrt p.$$
--   The bound is on the full complement of the constants for the counting inner product. It is unconditional: no automorphic theorem is a hypothesis. This is the sharp spectral input for the main theorem.
--
--   Differences from the source:
--   - encoding: the fixed arithmetic objects and labeled graphs → the shared concrete definitions over the quadratic algebra, ZMod residues, and zero-based Fin label indices; reason: the representations preserve the field, orders, incidences, and all source instances
--   - encoding: eigenvalue with an eigenvector in the orthogonal complement of 1 → a complex scalar and a nonzero complex eigenfunction with sum zero; reason: this spells out the eigenvalue and orthogonality conditions
-- source:
--   Olga Kharlampovich, Igor Pak, Alina Vdovina, STOC 2027 submission #136 (October 2026), source.pdf SHA-256 27d691a82d8af863e511e7e6b00cee95779d914645846d2974f876836db8f83b, p.19 (PDF p.20), Proposition 5.1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/136.pdf

import Definitions.Def_RamanujanLiftTower136_Tower_Graphs

namespace RamanujanLiftTower136.Tower

theorem mean_zero_spectral_bound (p n : ℕ) (hp : admissible p) (hn : 1 ≤ n)
    (lambda : ℂ) (h : Vertex n → ℂ) (hne : h ≠ 0)
    (hzero : ∑ t, h t = 0) (heigen : ∀ t, adjacency p n h t = lambda*h t) :
    ‖lambda‖ ≤ 2 * Real.sqrt p := by sorry

end RamanujanLiftTower136.Tower
