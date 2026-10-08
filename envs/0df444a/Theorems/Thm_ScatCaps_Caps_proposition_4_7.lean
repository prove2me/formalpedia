-- Prove2me | Theorems.Thm_ScatCaps_Caps_proposition_4_7
-- name    : ScatCaps.Caps.proposition_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:06:03.959478+00:00
-- url     : https://prove2.me/theorems/bb725fde-0a18-4858-a8bf-eebe78c71e12
-- title:
--   Proposition 4.7, p. 20 — a maximum scattered linear set of PG(2, q) yields a complete cap of size 2q^{(n−1)/2} in AG(n, q)
-- statement:
--   Let $q = 2^t$ with $t$ even, and let $n \ge 4$ be even. Suppose there is a maximum scattered linear set in $PG(2, q)$, i.e. an $\mathbb F_2$-subspace $U$ of $\mathbb F_q^3$ of rank $3t/2$ whose linear set $L_U$ is scattered. Then there exists a complete cap $S$ in $AG(n, q)$ with
--
--   $$|S| = 2\, q^{\frac{n-1}{2}} .$$
--
--   This is the conditional form of Theorem 1.3: it reduces the existence of small complete caps in even dimension to the existence of maximum scattered $\mathbb F_2$-linear sets in the plane.
--
--   **Formalization Note** "Maximum" is read as in the first line of the proof: the scattered $\mathbb F_2$-linear set has rank $3t/2$ (the largest rank, by Theorem 1.1); this avoids formalizing Theorem 1.1. The size is written $2 \cdot 2^{t(n-1)/2}$ with natural-number division, which is exact because $t$ is even, and equals $2q^{(n-1)/2}$.
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, p. 20, Proposition 4.7

import Mathlib
import Definitions.Def_ScatCaps_Caps_Model
import Definitions.Def_ScatCaps_LinearSets_Model

namespace ScatCaps.Caps

theorem proposition_4_7 (K : Type*) [Field K] [Fintype K] (t n : ℕ)
    (hK : Fintype.card K = 2 ^ t) (ht : Even t) (hn : 4 ≤ n) (hne : Even n)
    (hL : ∃ U : Set (Fin 3 → K), ScatCaps.LinearSets.IsFqSubspace (⊥ : Subfield K) U ∧
      ScatCaps.LinearSets.HasRank (⊥ : Subfield K) U (3 * t / 2) ∧
      ScatCaps.LinearSets.IsScattered (⊥ : Subfield K) (⊤ : Subfield K) U) :
    ∃ S : Set (Fin n → K), IsCompleteCap S ∧ S.ncard = 2 * 2 ^ (t * (n - 1) / 2) := by sorry

end ScatCaps.Caps
