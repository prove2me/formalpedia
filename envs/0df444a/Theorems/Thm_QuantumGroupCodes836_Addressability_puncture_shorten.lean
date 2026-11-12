-- Prove2me | Theorems.Thm_QuantumGroupCodes836_Addressability_puncture_shorten
-- name    : QuantumGroupCodes836.Addressability.puncture_shorten
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T17:07:34.818249+00:00
-- url     : https://prove2.me/theorems/1a62f396-02c1-46b7-b7b5-b48604b1377e
-- title:
--   Lemma 2.10 — puncture–shorten estimates (corrected: shortened distance bound)
-- statement:
--   Let $C\subseteq F^N$ be a finite-field linear code of length $n$, dimension $k$ and distance $d$, and let $L\subseteq N$ have size $\ell$. Puncturing and shortening both delete $L$. Their duality identities are
--
--   $$(C^\perp)_{L=0}=(C_J)^\perp,\qquad(C^\perp)_J=(C_{L=0})^\perp.$$
--
--   If $\ell<d$, the punctured dimension is $k$ and the shortened dual dimension is $n-\ell-k$. The shortened distance is at least $d$, and puncturing has distance at least $d-\ell$. This retains both dimension clauses and both distance bounds.
--
--   Differences from the source:
--   - encoding: finite coordinate sets and Hamming minima → zero-based finite types, actual submodules and extended-natural minima; reason: relabeling changes no code; the zero code has infinite distance
--   - correction: the shortened distance equals d → the shortened distance is at least d; reason: C1: over F2, span(11000,00111), puncturing L={1}, has distance 2 but its shortening has distance 3
-- source:
--   Virgile Guemard, Jean Gasnier, STOC 2027 submission #836 (October 2026), Lemma 2.10, p.6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/836.pdf

import Definitions.Def_QuantumGroupCodes836_Addressability_Linear

set_option autoImplicit false
open scoped Classical

namespace QuantumGroupCodes836.Addressability

theorem puncture_shorten {F : Type} [Field F] [Fintype F] {n : ℕ}
    (C : Code F (Fin n)) (L : Set (Fin n)) :
    shorten (dual C) L = dual (puncture C L) ∧
    puncture (dual C) L = dual (shorten C L) ∧
    ((Nat.card L : ℕ∞) < distance C →
      Module.finrank F (puncture C L) = Module.finrank F C ∧
      Module.finrank F (shorten (dual C) L) = n - Nat.card L - Module.finrank F C) ∧
    distance C ≤ distance (shorten C L) ∧
    distance C - (Nat.card L : ℕ∞) ≤ distance (puncture C L) := by sorry

end QuantumGroupCodes836.Addressability
