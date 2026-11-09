-- Prove2me | Theorems.Thm_RestrictedDec_coordinate_collisions
-- name    : RestrictedDec.coordinate_collisions
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:52:33.901037+00:00
-- url     : https://prove2.me/theorems/67f378ef-307f-429d-a884-657ce56a3c8d
-- title:
--   Proof of Corollary 2 — coordinate collisions $q_S(0^n)=q_S(e_j)$, $q_T(0^n)\ne q_T(e_j)$, $q_S(0^n)\ne q_S(e_i)$
-- statement:
--   Let $S_\lambda,T_\lambda\subseteq[n(\lambda)]$, let $i\in S_\lambda$ and $j\in T_\lambda\setminus S_\lambda$. Then
--
--   $$q_S(0^n)=q_S(e_j),\qquad q_T(0^n)\neq q_T(e_j),\qquad q_S(0^n)\neq q_S(e_i).$$
--
--   These three facts drive both constructions of Corollary 2: probes that decrypt to $0^n$ or $e_j$ look alike to a $q_S$-oracle but not to a $q_T$-oracle, and the wrap scheme's answers $0^n$ and $e_i$ are told apart by $q_S$.
--
--   Differences from the source:
--   - encoding: messages, keys, ciphertexts, pairs (β, c), positions in [n] → bit strings Str, (β, c) as β :: c, ⊥ as none, positions numbered from 1; reason: Lean convention; same instances
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), proof of Corollary 2, p.22 (qS(0n) = qS(ej), qT(0n) ≠ qT(ej)) and p.23 (qS(0n), qS(ei) differ)

import Mathlib
import Definitions.Def_RestrictedDec_unitVec
import Definitions.Def_RestrictedDec_qCoord
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

/-- **Coordinate collisions** (proof of Corollary 2, pp.22–23). Let `S_λ, T_λ ⊆ [n(λ)]`,
`i ∈ S_λ` and `j ∈ T_λ \ S_λ`. Then `q_S(0ⁿ) = q_S(e_j)`, `q_T(0ⁿ) ≠ q_T(e_j)` and
`q_S(0ⁿ) ≠ q_S(e_i)`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), proof of Corollary 2, p.22
("Since qS(0n) = qS(ej) … since qT(0n) ≠ qT(ej)") and p.23 ("The response is qS(0n) or qS(ei) …
As these two values differ"). -/
theorem coordinate_collisions (n : ℕ → ℕ) (S T : ℕ → Finset ℕ) (lam i j : ℕ)
    (hS : S lam ⊆ Finset.Icc 1 (n lam)) (hT : T lam ⊆ Finset.Icc 1 (n lam))
    (hi : i ∈ S lam) (hj : j ∈ T lam \ S lam) :
    qCoord S lam (some (zeros (n lam))) = qCoord S lam (some (unitVec (n lam) j)) ∧
      qCoord T lam (some (zeros (n lam))) ≠ qCoord T lam (some (unitVec (n lam) j)) ∧
      qCoord S lam (some (zeros (n lam))) ≠ qCoord S lam (some (unitVec (n lam) i)) := by sorry

end RestrictedDec
