-- Prove2me | Theorems.Thm_TensorRankN2M_ThreeTwoM_eq_1_2
-- name    : TensorRankN2M.ThreeTwoM.eq_1_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T04:17:59.227201+00:00
-- url     : https://prove2.me/theorems/3fc321fc-1dad-463c-ba2c-af2e1bee4073
-- title:
--   §4, Eq. (1)–(2) — (n−1)dim U + rk H ≤ rk L + (n−1)dim(ker W/J), hence R ≥ (n+2)m + (rk H − rk L)/(n−1)
-- statement:
--   Let $\mathbb F$ be algebraically closed, $n,m\ge 3$, and let $(\alpha_r,\beta_r,C_r)_{0\le r<R}$ be a strongly normalized $R$-rank decomposition of $\langle n,2,m\rangle$ over $\mathbb F$, with $U$, $J$, $W$, $L$, $H$ as in §4. Then
--   $$(n-1)\dim(U)+\operatorname{rk}(H)\le \operatorname{rk}(L)+(n-1)\dim(\ker(W)/J)\tag{1}$$
--   and
--   $$R\ \ge\ (n+2)m+\frac{\operatorname{rk}(H)-\operatorname{rk}(L)}{n-1}.\tag{2}$$
--   Here $\operatorname{rk}$ is the dimension of the image. The paper derives (1) from Lemma 10 by comparing dimensions and (2) from (1) using $\dim U=m$ and $\dim(\ker(W)/J)=R-(n+1)m$. These are the base inequalities of both main theorems; for $n=3$ the term $\operatorname{rk}(H)-\operatorname{rk}(L)$ may be negative, which is why §4.1 refines the count.
--
--   Differences from the source:
--   - reading: the displayed derivation carries no hypotheses → 𝔽 algebraically closed, the decomposition strongly normalized, n, m ≥ 3; reason: §2's standing assumptions (p. 2), §3's strong normalization (p. 4) and §4's m, n ≥ 3 (p. 4) are in force; §2's other assumption, no α_r identically 0, is not a separate hypothesis because strong normalization implies it (D(e_{0,0}) invertible)
--   - encoding: rk(L), rk(H) as dimensions of images in ker(W)/J and (ker(W)/J)^{n−1} → dimensions of the ranges of L, H with codomains 𝔽^R/J and (𝔽^R/J)^{n−1}; reason: the paper's codomains are subspaces, so the images are the same spaces
--   - encoding: ker(W)/J → ker W modulo J ∩ ker W (KerWModJ); reason: J ⊆ ker W (p. 3), so this is the same quotient
--   - encoding: (1) and (2) as two displayed inequalities → one conjunction, (1) in ℕ (n − 1 with n ≥ 3 is not truncated) and (2) in ℚ; reason: (2) divides by n − 1
-- source:
--   Jason Yang, New lower bounds on tensor rank of (n,2,m) matrix multiplication with GPT-6 Astra, STOC 2027 submission (manuscript of October 2026, sha256 6c1df229…), p. 5, §4, Eq. (1)–(2)

import Mathlib
import Definitions.Def_TensorRankN2M_ThreeTwoM_Decomposition
import Definitions.Def_TensorRankN2M_ThreeTwoM_Normalization
import Definitions.Def_TensorRankN2M_ThreeTwoM_SkewAugmentation
import Definitions.Def_TensorRankN2M_ThreeTwoM_N2M

namespace TensorRankN2M.ThreeTwoM

/-- §4, Eq. (1) and Eq. (2) (p. 5): for a strongly normalized decomposition of ⟨n,2,m⟩ with
`n, m ≥ 3` (under the standing assumption of §2 that `𝔽` is algebraically closed; §2's other assumption,
no `α_r` constant `0`, is implied by strong normalization),
`(n−1)dim(U) + rk(H) ≤ rk(L) + (n−1)dim(ker(W)/J)` (1) and
`R ≥ (n+2)m + (rk(H) − rk(L))/(n−1)` (2). -/
theorem eq_1_2 {𝔽 : Type*} [Field 𝔽] [IsAlgClosed 𝔽] {n m R : ℕ} [NeZero n]
    (hn : 3 ≤ n) (hm : 3 ≤ m) (d : Decomposition 𝔽 n 2 m R)
    (hd : d.StronglyNormalized) :
    (n - 1) * Module.finrank 𝔽 (U 𝔽 m) + Module.finrank 𝔽 (LinearMap.range d.H) ≤
        Module.finrank 𝔽 (LinearMap.range d.L) + (n - 1) * Module.finrank 𝔽 d.KerWModJ ∧
      ((n : ℚ) + 2) * m +
          ((Module.finrank 𝔽 (LinearMap.range d.H) : ℚ) -
            Module.finrank 𝔽 (LinearMap.range d.L)) / ((n : ℚ) - 1) ≤ R := by sorry

end TensorRankN2M.ThreeTwoM
