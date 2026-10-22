-- Prove2me | Theorems.Thm_PTCommutant_OperatorBasis_lemma_26
-- name    : PTCommutant.OperatorBasis.lemma_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:29:30.056857+00:00
-- url     : https://prove2.me/theorems/b6248b7c-4a26-4c4b-81db-93ad1b389e81
-- title:
--   Lemma 26, p. 16 — V′(σ_ab) = Π_b V(f_ab⁻¹(σ_ab)) V′(n n−1) Π_a⁻¹ with f_ab⁻¹(σ_ab) ∈ S(n−2)
-- statement:
--   Fix $\pi_1,\dots,\pi_{n-1}\in S(n-1)$ with $\pi_k(n-1)=k$ for every $k$ (Definition 24), and write $\Pi_k=V(\pi_k)$. Let $a,b\in\{1,\dots,n-1\}$ and let $\sigma_{ab}\in S(n)$ satisfy $\sigma_{ab}(a)=n$ and $\sigma_{ab}(n)=b$ (Notation 1). Then the permutation
--   $$f^{-1}_{ab}(\sigma_{ab})=\pi_b^{-1}\circ\sigma_{ab}\circ\pi_a\circ(n\ n-1)$$
--   fixes the systems $n-1$ and $n$, i.e. lies in $S(n-2)$, and
--   $$V'(\sigma_{ab})=\Pi_b\,V\big(f^{-1}_{ab}(\sigma_{ab})\big)\,V'(n\ n-1)\,\Pi_a^{-1}.$$
--
--   The lemma reduces every partially transposed permutation operator that moves the last system to one fixed operator $V'(n\ n-1)$, dressed by permutations of $S(n-1)$; it is the bridge from $\mathbb C[S(n-2)]$ to $\mathcal A$ used in the proof of Theorem 9.
--
--   **Formalization Note.** $n=m+2$; labels $a,b$ are `Fin (m+1)` and their system index in `Fin (m+2)` is `a.castSucc`; system $n$ is `Fin.last (m+1)`. "$f^{-1}_{ab}(\sigma_{ab})\in S(n-2)$" is stated as the existence of $\sigma\in S(n-2)$ whose embedding `liftPerm m 2 σ` equals that product. The hypotheses follow Notation 1 ($n=\sigma(a)$, $b=\sigma(n)$); eq. (11) of the paper prints "$\sigma_{ab}(n)=a$, $\sigma^{-1}_{ab}[n]=b$", which contradicts Notation 1 and eq. (7) and is treated as a misprint.
-- source:
--   Studziński, Horodecki, Mozrzymas, Commutant structuture of U⊗(n−1)⊗U* transformations, arXiv:1305.6183v2, p. 16, Lemma 26 (eq. (81)); proof p. 17; Notation 1 p. 4; Definition 24 p. 15

import Mathlib
import Definitions.Def_PTCommutant_OperatorBasis_Model

namespace PTCommutant.OperatorBasis
open QAlgorithms.Schur

theorem lemma_26 {m d : ℕ} (π : Fin (m + 1) → Equiv.Perm (Fin (m + 1)))
    (hπ : ∀ k, π k (Fin.last m) = k) (a b : Fin (m + 1)) (τ : Equiv.Perm (Fin (m + 2)))
    (ha : τ a.castSucc = Fin.last (m + 1)) (hb : τ (Fin.last (m + 1)) = b.castSucc) :
    ∃ σ : Equiv.Perm (Fin m),
      liftPerm m 2 σ =
          (liftPerm (m + 1) 1 (π b))⁻¹ * τ * liftPerm (m + 1) 1 (π a) * swapLast m ∧
        ptLast (tensorPermutation d (m + 2) τ) =
          tensorPermutation d (m + 2) (liftPerm (m + 1) 1 (π b)) *
            tensorPermutation d (m + 2) (liftPerm m 2 σ) *
            ptLast (tensorPermutation d (m + 2) (swapLast m)) *
            tensorPermutation d (m + 2) ((liftPerm (m + 1) 1 (π a))⁻¹) := by sorry

end PTCommutant.OperatorBasis
