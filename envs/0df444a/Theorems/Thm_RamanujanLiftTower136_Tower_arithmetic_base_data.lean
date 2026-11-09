-- Prove2me | Theorems.Thm_RamanujanLiftTower136_Tower_arithmetic_base_data
-- name    : RamanujanLiftTower136.Tower.arithmetic_base_data
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:39:23.559199+00:00
-- url     : https://prove2.me/theorems/1bbe0491-c0cd-4758-87db-2c6799c565d5
-- title:
--   Proposition 3.3 — narrow class number, scalar units, and class count
-- statement:
--   The field $F=\mathbb Q(\sqrt{17})$ has narrow class number one. For every integer $m\ge2$ and every Eichler order $A$ of level $Q^m$, all its units are scalar, as are all units of the left order of every locally principal right $A$-ideal. Moreover, for every $n\ge0$,
--   $$|\mathrm{Cl}(E_n)|=2^n,\qquad E_0^\times=O_F^\times.$$
--   Here ideal classes mean actual locally principal quaternion ideals modulo multiplication by $D^\times$. This statement supplies the complete class count and the absence of projective stabilizers.
--
--   Differences from the source:
--   - encoding: the fixed arithmetic objects and labeled graphs → the shared concrete definitions over the quadratic algebra, ZMod residues, and zero-based Fin label indices; reason: the representations preserve the field, orders, incidences, and all source instances
--   - encoding: narrow class number one and scalar units → every nonzero integral ideal has a totally positive generator, and units of each order are precisely embedded OF units; reason: these are the defining properties rather than numerical class-group or unit-group abbreviations
-- source:
--   Olga Kharlampovich, Igor Pak, Alina Vdovina, STOC 2027 submission #136 (October 2026), source.pdf SHA-256 27d691a82d8af863e511e7e6b00cee95779d914645846d2974f876836db8f83b, p.13 (PDF p.14), Proposition 3.3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/136.pdf

import Definitions.Def_RamanujanLiftTower136_Tower_Ideals

namespace RamanujanLiftTower136.Tower

theorem arithmetic_base_data :
  narrowClassOne ∧
  (∀ (A : Set D) (m : ℕ), 2 ≤ m → eichlerLevel A m →
    onlyScalarUnits A ∧ ∀ I, locallyPrincipal A I → onlyScalarUnits (leftOrder I)) ∧
  (∀ n : ℕ, Nat.card (ClassSet (levelOrder n)) = 2^n) ∧
  onlyScalarUnits (levelOrder 0) := by sorry

end RamanujanLiftTower136.Tower
