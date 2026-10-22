-- Prove2me | Theorems.Thm_PTCommutant_OperatorBasis_eq_9
-- name    : PTCommutant.OperatorBasis.eq_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T09:29:31.652996+00:00
-- url     : https://prove2.me/theorems/c30a4a30-2412-4ef3-bcfa-054375a3ad67
-- title:
--   Eq. (9), p. 4 — S(n) = ⋃_{a,b} S_ab ∪ S(n−1), the S_ab pairwise disjoint, and S_ab ≅ S(n−2) via f_ab
-- statement:
--   Fix $\pi_1,\dots,\pi_{n-1}\in S(n-1)$ with $\pi_k(n-1)=k$, and let $f_{ab}(\sigma)=\pi_b\circ\sigma\circ(n\ n-1)\circ\pi_a^{-1}$ for $\sigma\in S(n-2)$ and $a,b\in\{1,\dots,n-1\}$ (eq. (7)). Put $S_{ab}=f_{ab}(S(n-2))$. Then
--
--   1. every $\tau\in S(n)$ with $\tau(n)\neq n$ equals $f_{ab}(\sigma)$ for **exactly one** triple $(a,b,\sigma)$;
--   2. $f_{ab}(\sigma)(n)\neq n$ for every triple;
--   3. $\tau(n)=n$ if and only if $\tau\in S(n-1)$.
--
--   Together these say
--   $$S(n)=\bigcup_{a,b=1}^{n-1}S_{ab}\,\cup\,S(n-1),\qquad S_{ab}\cap S_{cd}=\emptyset\ \text{for }ab\neq cd,$$
--   with the union disjoint from $S(n-1)$, and that each $f_{ab}$ is a bijection $S(n-2)\to S_{ab}$. This partition is what lets Theorem 9(b) cover every partially transposed permutation operator outside $\mathbb C[S(n-1)]$.
--
--   **Formalization Note.** $n=m+2$; labels are `Fin (m+1)`, system $n$ is `Fin.last (m+1)`, and $S(n-1)$ is the range of `liftPerm (m+1) 1`. Clause 1 is an `∃!` over triples in `Fin (m+1) × Fin (m+1) × Equiv.Perm (Fin m)`, which encodes covering, pairwise disjointness and injectivity of each $f_{ab}$ at once.
-- source:
--   Studziński, Horodecki, Mozrzymas, Commutant structuture of U⊗(n−1)⊗U* transformations, arXiv:1305.6183v2, p. 4, eq. (9) and the sentence following it; eq. (7) p. 4; Definition 24 p. 15

import Mathlib
import Definitions.Def_PTCommutant_OperatorBasis_Model

namespace PTCommutant.OperatorBasis

theorem eq_9 {m : ℕ} (π : Fin (m + 1) → Equiv.Perm (Fin (m + 1)))
    (hπ : ∀ k, π k (Fin.last m) = k) :
    (∀ τ : Equiv.Perm (Fin (m + 2)), τ (Fin.last (m + 1)) ≠ Fin.last (m + 1) →
      ∃! t : Fin (m + 1) × Fin (m + 1) × Equiv.Perm (Fin m), fPerm π t.1 t.2.1 t.2.2 = τ) ∧
    (∀ (a b : Fin (m + 1)) (σ : Equiv.Perm (Fin m)),
      fPerm π a b σ (Fin.last (m + 1)) ≠ Fin.last (m + 1)) ∧
    (∀ τ : Equiv.Perm (Fin (m + 2)),
      τ (Fin.last (m + 1)) = Fin.last (m + 1) ↔ τ ∈ Set.range (liftPerm (m + 1) 1)) := by sorry

end PTCommutant.OperatorBasis
