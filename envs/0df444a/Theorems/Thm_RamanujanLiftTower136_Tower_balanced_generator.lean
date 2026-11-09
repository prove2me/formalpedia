-- Prove2me | Theorems.Thm_RamanujanLiftTower136_Tower_balanced_generator
-- name    : RamanujanLiftTower136.Tower.balanced_generator
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:44:23.165615+00:00
-- url     : https://prove2.me/theorems/67d223b2-f358-4706-9a66-8894f12d3105
-- title:
--   Lemma 7.1 — a balanced generator
-- statement:
--   For every admissible prime $p$, the specified generator $\pi$ of $P$ is totally positive. With $\pi_1=\tau_+(\pi)$, $\pi_2=\tau_-(\pi)$, and $\varepsilon_0=4+\sqrt{17}$,
--   $$\varepsilon_0^{-1}\sqrt p\le\pi_i\le\varepsilon_0\sqrt p\quad(i=1,2).$$
--   It is the first solution of the exact tests (7.2) in the prescribed box. From binary $p$ and the supplied smaller residue root $s_p$, a single finite-alphabet multi-stack machine outputs its two integer coordinates in at most $Cp(\lfloor\log_2p\rfloor+1)^k$ steps, for absolute $C>0$ and $k$. This supplies a deterministic balanced generator, uniformly in the degree.
--
--   Differences from the source:
--   - encoding: the fixed arithmetic objects and labeled graphs → the shared concrete definitions over the quadratic algebra, ZMod residues, and zero-based Fin label indices; reason: the representations preserve the field, orders, incidences, and all source instances
--   - reading: lexicographically first and lexicographically sorted integer coordinates → the usual signed-integer lexicographic order on pairs and eight-tuples; reason: the paper does not specify the order on signed coordinate vectors more explicitly
--   - reading: bit operations → steps of a finite-alphabet finite-control multi-stack machine with the stated binary encodings; reason: schoolbook arithmetic and bitwise Hensel lifting retain the cubic bound; fixed-prime lookup is absorbed only in its permitted constant
--   - encoding: O(p) poly(log p) → existential positive C and natural k before all admissible primes, and the exact upper bound C p (floor(log2 p)+1)^k; reason: changing log base and adding one preserves the uniform asymptotic assertion
--   - reading: a totally positive balanced generator can be chosen and found deterministically → the lexicographically first solution of (7.2) in the box |a|,|b| ≤ 20⌈√p⌉ is a totally positive balanced generator of P, and the machine outputs exactly it; reason: this is the deterministic convention fixed in the proof of Lemma 7.1 and used by §7 and Theorem 1.1; it implies the existential statement
-- source:
--   Olga Kharlampovich, Igor Pak, Alina Vdovina, STOC 2027 submission #136 (October 2026), source.pdf SHA-256 27d691a82d8af863e511e7e6b00cee95779d914645846d2974f876836db8f83b, p.21 (PDF p.22), Lemma 7.1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/136.pdf

import Definitions.Def_RamanujanLiftTower136_Tower_Ideals
import Definitions.Def_RamanujanLiftTower136_Tower_Computation

namespace RamanujanLiftTower136.Tower

theorem balanced_generator :
  balancedAlgorithm ∧ ∀ p : ℕ, admissible p →
    totallyPositive (primeGenerator p) ∧
    principalIdeal (primeGenerator p) = idealAsModule (P p) ∧
    (∀ y ∈ ({tauPlus (primeGenerator p), tauMinus (primeGenerator p)} : Set ℝ),
      (4 + Real.sqrt 17)⁻¹ * Real.sqrt p ≤ y ∧ y ≤ (4 + Real.sqrt 17) * Real.sqrt p) ∧
    generatorTest p (smallerRoot p) (balancedCoordinates p (smallerRoot p)) := by sorry

end RamanujanLiftTower136.Tower
