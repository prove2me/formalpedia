-- Prove2me | Theorems.Thm_QuantumGroupCodes836_Addressability_lower_multiplication
-- name    : QuantumGroupCodes836.Addressability.lower_multiplication
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T17:07:33.347985+00:00
-- url     : https://prove2.me/theorems/1eeb2f36-1ada-4ad2-af71-524d6cfc878b
-- title:
--   Lemma 2.8 — lower multiplication properties
-- statement:
--   Let $C\subseteq F^n$ be a finite-field linear code containing the all-one word, and let $u$ have nonzero coordinates. Suppose $u\star C^{\star m}\subseteq C^\perp$, where $m\ge1$. Then the same weights work for every lower positive degree:
--
--   $$u\star C^{\star a}\subseteq C^\perp\qquad(1\le a\le m).$$
--
--   This preserves the common weight vector needed by the family of lower-arity gates.
--
--   Differences from the source:
--   - encoding: finite coordinate sets and Hamming minima → zero-based finite types, actual submodules and extended-natural minima; reason: relabeling changes no code; the zero code has infinite distance
--   - generalization: C satisfies the m̃-multiplication property for some nonzero weight vector → the same weight vector u works for every 1 ≤ a ≤ m; reason: since the all-one word lies in C, u⋆C^{⋆a} ⊆ u⋆C^{⋆m} ⊆ C^⊥; the Lean conclusion implies the source one
-- source:
--   Virgile Guemard, Jean Gasnier, STOC 2027 submission #836 (October 2026), Lemma 2.8, p.6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/836.pdf

import Definitions.Def_QuantumGroupCodes836_Addressability_Linear

set_option autoImplicit false

namespace QuantumGroupCodes836.Addressability

theorem lower_multiplication {F : Type} [Field F] [Fintype F] {n m : ℕ}
    (C : Code F (Fin n)) (u : Fin n → F)
    (hm : 1 ≤ m) (h : MultiplicationWith C m u) (h1 : (1 : Fin n → F) ∈ C) :
    ∀ a : ℕ, 1 ≤ a → a ≤ m → MultiplicationWith C a u := by sorry

end QuantumGroupCodes836.Addressability
