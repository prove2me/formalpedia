-- Prove2me | Theorems.Thm_RamanujanLiftTower136_Tower_norm_generators
-- name    : RamanujanLiftTower136.Tower.norm_generators
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:39:50.549393+00:00
-- url     : https://prove2.me/theorems/331f6a72-fbb1-4bb7-9656-bf2b67104733
-- title:
--   Lemma 4.1 — norm generators
-- statement:
--   Let $p\equiv1\pmod{17}$ be prime, let $P=(p,\omega-s_p)$, and let $\pi$ be any totally positive generator of $P$. For $E_0=O_F\langle1,\eta i,\eta u,v\rangle$, define
--   $$S_p=\{x\in E_0:\operatorname{nrd}(x)=\pi\}/\{\pm1\}.$$
--   Then $|S_p|=p+1$. Its image in $D^\times/F^\times$ is closed under inversion. Every representative is invertible in the completed order $(E_0)_Q$ and reduces to a scalar matrix modulo $2$ under $\psi$. This explains both the number of edge labels and the projective inverse pairing.
--
--   Differences from the source:
--   - encoding: the fixed arithmetic objects and labeled graphs → the shared concrete definitions over the quadratic algebra, ZMod residues, and zero-based Fin label indices; reason: the representations preserve the field, orders, incidences, and all source instances
--   - encoding: projective inversion and local order units → existence of a nonzero scalar multiple of the explicit quaternion inverse, and matrix units with inverse in the completed base order; reason: this states exactly the quotient and invertibility properties without assuming them
-- source:
--   Olga Kharlampovich, Igor Pak, Alina Vdovina, STOC 2027 submission #136 (October 2026), source.pdf SHA-256 27d691a82d8af863e511e7e6b00cee95779d914645846d2974f876836db8f83b, p.16 (PDF p.17), Lemma 4.1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/136.pdf

import Definitions.Def_RamanujanLiftTower136_Tower_Ideals

namespace RamanujanLiftTower136.Tower

theorem norm_generators (p : ℕ) (hp : admissible p) (pi : F)
    (hpositive : totallyPositive pi) (hprincipal : principalIdeal pi = idealAsModule (P p)) :
  Nat.card (SignClass pi) = p+1 ∧
  (∀ x : D, x ∈ baseLattice → nrd x = pi →
    ∃ y : D, y ∈ baseLattice ∧ nrd y = pi ∧
      ∃ a : F, a ≠ 0 ∧ y = a • inverseQuaternion x) ∧
  ∀ x : D, x ∈ baseLattice → nrd x = pi →
    (∃ g : (Matrix (Fin 2) (Fin 2) ℚ_[2])ˣ,
      (g : Matrix (Fin 2) (Fin 2) ℚ_[2]) = psi x ∧
      (g : Matrix (Fin 2) (Fin 2) ℚ_[2]) ∈ dyadicOrder 0 ∧
      ((g⁻¹ : (Matrix (Fin 2) (Fin 2) ℚ_[2])ˣ) : Matrix (Fin 2) (Fin 2) ℚ_[2]) ∈ dyadicOrder 0) ∧
    (∀ i j, PadicInt.toZModPow 1 (toPadicInt (psi x i j)) = if i = j then 1 else 0) := by sorry

end RamanujanLiftTower136.Tower
