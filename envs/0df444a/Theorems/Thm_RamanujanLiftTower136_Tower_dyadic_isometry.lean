-- Prove2me | Theorems.Thm_RamanujanLiftTower136_Tower_dyadic_isometry
-- name    : RamanujanLiftTower136.Tower.dyadic_isometry
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:34:59.597529+00:00
-- url     : https://prove2.me/theorems/f12a3d88-7738-4350-ab57-942ce532ded8
-- title:
--   Lemma 6.1 — dyadic isometry
-- statement:
--   Let $p\equiv1\pmod{17}$ be prime, and let $g_j=\psi(\overline{x_j})$ be any of the chosen neighbor matrices. For every two distinct $t,u\in\mathbb Z_2$, their images are distinct and
--   $$v_2(\varphi_{g_j}(t)-\varphi_{g_j}(u))=v_2(t-u).$$
--   This preserves both shared binary digits and the first differing digit. It is the local property behind the two-sheeted covers.
--
--   Differences from the source:
--   - encoding: the fixed arithmetic objects and labeled graphs → the shared concrete definitions over the quadratic algebra, ZMod residues, and zero-based Fin label indices; reason: the representations preserve the field, orders, incidences, and all source instances
--   - encoding: valuation of the nonzero difference of the images → explicit distinctness of the images followed by equality of natural-valued PadicInt valuations; reason: Mathlib assigns valuation zero to zero; the nonzero conclusion preserves the source valuation convention
-- source:
--   Olga Kharlampovich, Igor Pak, Alina Vdovina, STOC 2027 submission #136 (October 2026), source.pdf SHA-256 27d691a82d8af863e511e7e6b00cee95779d914645846d2974f876836db8f83b, p.20 (PDF p.21), Lemma 6.1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/136.pdf

import Definitions.Def_RamanujanLiftTower136_Tower_Construction

namespace RamanujanLiftTower136.Tower

theorem dyadic_isometry (p : ℕ) (hp : admissible p) (j : Label p)
    (t u : ℤ_[2]) (htu : t ≠ u) :
  phi (neighborMatrix p j) t ≠ phi (neighborMatrix p j) u ∧
  (phi (neighborMatrix p j) t - phi (neighborMatrix p j) u).valuation = (t-u).valuation := by sorry

end RamanujanLiftTower136.Tower
