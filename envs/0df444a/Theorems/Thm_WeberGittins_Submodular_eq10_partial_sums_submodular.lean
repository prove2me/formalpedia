-- Prove2me | Theorems.Thm_WeberGittins_Submodular_eq10_partial_sums_submodular
-- name    : WeberGittins.Submodular.eq10_partial_sums_submodular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:55:57.298618+00:00
-- url     : https://prove2.me/theorems/5075ed23-78f6-4a78-b11b-193341aecf82
-- title:
--   Proof of Theorem 4, eq. (10) — $U_t(I\cap J)+U_t(I\cup J)\le U_t(I)+U_t(J)$
-- statement:
--   Let $H_j=(H_{j0},H_{j1},\dots)$, $j\in\{1,\dots,n\}$, be sequences of real numbers that are **nonincreasing** ($H_{j0}\ge H_{j1}\ge\cdots$) and **nonnegative**. For a set of bandits $I$ and $t\ge0$, let $U_t(I)$ be the sum of the first $t$ terms of the interleaving of the sequences $H_j$, $j\in I$, into nonincreasing order ($U_t(\emptyset)=0$). Then for all sets $I,J\subseteq\{1,\dots,n\}$ and all $t\ge0$,
--   $$
--   U_t(I\cap J)+U_t(I\cup J)\le U_t(I)+U_t(J).
--   $$
--
--   This is inequality (10) in the proof of Weber's Theorem 4, stated for one fixed realisation of the bandits' state sequences, where $H_{jk}=\gamma_{jk}$ are the prevailing charges. It is a purely deterministic statement about sums of largest terms; summed against $\beta^t$ and averaged over realisations it yields the submodularity of the optimal value.
--
--   **Formalization Note** $U_t(I)$ is `partialInterleavedSum H I t`, the largest sum of initial segments of total length $t$ (equal to the interleaving sum for nonincreasing sequences). Nonnegativity of the sequences is Weber's standing assumption of nonnegative rewards (p. 1024), which makes the fair charges nonnegative; it is needed when $I\cap J=\emptyset$ (for $t=1$, $I=\{a\}$, $J=\{b\}$ and $H_{a0}=H_{b0}=-5$, the left side is $-5$ and the right side $-10$).
-- source:
--   Weber, On the Gittins index for multiarmed bandits, Ann. Appl. Probab. 2 (1992), p. 1030, proof of Theorem 4, eq. (10)

import Definitions.Def_WeberGittins_Submodular_PartialInterleavedSum

namespace WeberGittins.Submodular

/-- Weber (1992), proof of Theorem 4, eq. (10), p. 1030: for nonincreasing, nonnegative
prevailing-charge sequences `H j`, the partial interleaved sums are submodular in the set of
bandits: `U_t(I ∩ J) + U_t(I ∪ J) ≤ U_t(I) + U_t(J)` for all `t ≥ 0`. -/
theorem eq10_partial_sums_submodular {n : ℕ} (H : Fin n → ℕ → ℝ)
    (hanti : ∀ j, Antitone (H j)) (hnonneg : ∀ j k, 0 ≤ H j k)
    (I J : Finset (Fin n)) (t : ℕ) :
    partialInterleavedSum H (I ∩ J) t + partialInterleavedSum H (I ∪ J) t ≤
      partialInterleavedSum H I t + partialInterleavedSum H J t := by sorry

end WeberGittins.Submodular
