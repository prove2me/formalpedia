-- Prove2me | Theorems.Thm_RamanujanLiftTower136_Tower_local_to_global_lattices
-- name    : RamanujanLiftTower136.Tower.local_to_global_lattices
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:39:47.737201+00:00
-- url     : https://prove2.me/theorems/01559cff-3739-4272-949b-533aa148d6fd
-- title:
--   Lemma 3.2 — local-to-global lattices
-- statement:
--   For each finite place $R$ of $F$, let $\Lambda_R\subset D_R$ be a full completed-integer lattice. Assume $\Lambda_R=O_R$ outside a finite set of places. Then
--   $$\Lambda=\{x\in D:\ x_R\in\Lambda_R\text{ for every }R\}$$
--   is a full $O_F$-lattice with exactly these completions, and every full lattice having these completions equals $\Lambda$. If the local lattices are right ideals of the completions of a fixed order $A$, then $\Lambda$ is a right $A$-ideal. This is the independent patching statement for the arithmetic construction.
--
--   Differences from the source:
--   - encoding: intersection of local lattices in D → the set of global quaternions whose diagonal images lie in every prescribed completed lattice; reason: completion is closure in the four-coordinate topology; finite generation and full span are explicit
-- source:
--   Olga Kharlampovich, Igor Pak, Alina Vdovina, STOC 2027 submission #136 (October 2026), source.pdf SHA-256 27d691a82d8af863e511e7e6b00cee95779d914645846d2974f876836db8f83b, p.13 (PDF p.14), Lemma 3.2. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/136.pdf

import Definitions.Def_RamanujanLiftTower136_Tower_Ideals

namespace RamanujanLiftTower136.Tower

theorem local_to_global_lattices
    (L : (R : Place) → Set (LocalD R))
    (hfull : ∀ R, localFullLattice R (L R))
    (hfinite : {R | L R ≠ completed (orderLattice : Set D) R}.Finite) :
    let A : Set D := {x | ∀ R, localize R x ∈ L R}
    fullLattice A ∧ (∀ R, completed A R = L R) ∧
    (∀ B : Set D, fullLattice B → (∀ R, completed B R = L R) → B = A) ∧
    ∀ B : Set D, isOrder B →
      (∀ R, localRightIdeal R (completed B R) (L R)) → rightIdeal B A := by sorry

end RamanujanLiftTower136.Tower
