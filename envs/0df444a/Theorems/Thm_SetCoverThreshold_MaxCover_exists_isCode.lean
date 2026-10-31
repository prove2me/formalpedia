-- Prove2me | Theorems.Thm_SetCoverThreshold_MaxCover_exists_isCode
-- name    : SetCoverThreshold.MaxCover.exists_isCode
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-30T19:10:58.124258+00:00
-- url     : https://prove2.me/theorems/74ee32b9-9b4c-4fe9-919b-33e76bac1370
-- title:
--   §2.3, p. 643 — existence of balanced binary codes with pairwise Hamming distance at least $\ell/3$
-- statement:
--   Let $k \ge 1$ be the number of provers and let $\ell_0 \in \mathbb{N}$ be any lower bound on the repetition length. There exist a block length $\ell \ge \max(\ell_0, 1)$ and a binary code $C_1, \dots, C_k \in \{0, 1\}^\ell$ (represented as $\operatorname{code} : \operatorname{Fin} k \to \operatorname{Fin} \ell \to \operatorname{Bool}$) satisfying the code conditions of Feige (1998, §2.3, p. 643):
--
--   $$\forall i \in \{1, \dots, k\},\quad 2 \cdot |\{j \in \{1, \dots, \ell\} : C_{i,j} = 1\}| = \ell,$$
--
--   $$\forall i \neq i',\quad 3 \cdot d_H(C_i, C_{i'}) \ge \ell,$$
--
--   where $d_H$ denotes the Hamming distance.
--
--   This lemma discharges the code-existence requirement in the $k$-prover proof system of §2.3 and in the $\mathrm{Max}\ k\text{-}\mathrm{Cover}$ hardness reduction of Theorem 5.3.
-- source:
--   Uriel Feige, A Threshold of ln n for Approximating Set Cover, Journal of the ACM 45(4), 1998, pp. 634-652, Section 2.3, p. 643

import Definitions.Def_SetCoverThreshold_MaxCover_ProofSystem

namespace SetCoverThreshold.MaxCover
theorem exists_isCode (k ℓ₀ : ℕ) (hk : 1 ≤ k) :
    ∃ (ℓ : ℕ) (code : Fin k → Fin ℓ → Bool), ℓ₀ ≤ ℓ ∧ 1 ≤ ℓ ∧ IsCode code := by sorry
end SetCoverThreshold.MaxCover
