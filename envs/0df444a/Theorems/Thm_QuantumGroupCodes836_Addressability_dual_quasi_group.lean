-- Prove2me | Theorems.Thm_QuantumGroupCodes836_Addressability_dual_quasi_group
-- name    : QuantumGroupCodes836.Addressability.dual_quasi_group
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T17:07:43.080278+00:00
-- url     : https://prove2.me/theorems/7cc3ccd2-2402-4690-8bad-009af7e490b7
-- title:
--   Lemma 2.2 — dual quasi-group stability
-- statement:
--   Let $C\subseteq F^n$ be a code over any finite field and let a finite group $G$ act by a specified faithful free coordinate action preserving $C$. Its Euclidean dual is preserved by the same action:
--
--   $$C^\perp\text{ is a quasi-}G\text{ code}.$$
--
--   Neither commutativity of $G$ nor characteristic two is required. The conclusion explicitly identifies the two coordinate homomorphisms, so it cannot be witnessed by an unrelated group action.
--
--   Differences from the source:
--   - encoding: finite coordinate sets and Hamming minima → zero-based finite types, actual submodules and extended-natural minima; reason: relabeling changes no code; the zero code has infinite distance
-- source:
--   Virgile Guemard, Jean Gasnier, STOC 2027 submission #836 (October 2026), Lemma 2.2, p.4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/836.pdf

import Definitions.Def_QuantumGroupCodes836_Addressability_Linear

set_option autoImplicit false

namespace QuantumGroupCodes836.Addressability

theorem dual_quasi_group {F G : Type} [Field F] [Fintype F] [Group G] [Fintype G]
    {n : ℕ} (C : Code F (Fin n)) (A : CodeAction F (Fin n) G C) :
    ∃ B : CodeAction F (Fin n) G (dual C), B.coordinates = A.coordinates := by sorry

end QuantumGroupCodes836.Addressability
