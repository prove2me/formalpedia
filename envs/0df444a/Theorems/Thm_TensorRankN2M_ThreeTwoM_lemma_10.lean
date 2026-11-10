-- Prove2me | Theorems.Thm_TensorRankN2M_ThreeTwoM_lemma_10
-- name    : TensorRankN2M.ThreeTwoM.lemma_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:17:50.292243+00:00
-- url     : https://prove2.me/theorems/fef4f62a-a8cf-4645-80a7-533a2d0362fb
-- title:
--   Lemma 10 — the kernel of Φ is 0 ⊕ ker(H)
-- statement:
--   Let $\mathbb F$ be algebraically closed, $n,m\ge 3$, and let $(\alpha_r,\beta_r,C_r)_{0\le r<R}$ be a strongly normalized $R$-rank decomposition of $\langle n,2,m\rangle$ over $\mathbb F$. With $U$, $J$, $g$, $\ell$, $h$, $L$, $H$ and
--   $$\Phi(u,c)=\big(\ell(u),\ \dots,\ -g(u_i)+h(c)_i,\ \dots\big)_{1\le i<n}+_{\mathrm{elt}}J,\qquad u\in U^{n-1},\ c\in U^{\wedge(n-1)},$$
--   as in §4, the kernel of $\Phi$ is
--   $$\ker(\Phi)=0\oplus\ker(H),$$
--   that is, $\Phi(u,c)=0$ if and only if $u=0$ and $H(c)=0$.
--
--   Comparing dimensions in this identity gives Eq. (1)–(2), the basic lower bound on $R$ for $\langle n,2,m\rangle$.
--
--   Differences from the source:
--   - reading: the lemma's sentence carries no hypotheses → 𝔽 algebraically closed, the decomposition strongly normalized, n, m ≥ 3; reason: §2's standing assumptions (p. 2), §3's strong normalization (p. 4) and §4's "for the ⟨n,2,m⟩ tensor with m, n ≥ 3" (p. 4) are in force; §2's other assumption, no α_r identically 0, is not a separate hypothesis because strong normalization implies it (D(e_{0,0}) invertible)
--   - encoding: ℓ into ker(W), L into ker(W)/J, Φ into im(L) ⊕ (ker(W)/J)^{n−1} → ℓ into 𝔽^R, L into 𝔽^R/J, Φ into (𝔽^R/J) × (𝔽^R/J)^{n−1}; reason: the paper's codomains are subspaces of the Lean ones (f_i(U), g(U) ⊆ ker W, p. 3), so the kernel is unchanged
--   - encoding: indices 1, …, n−1 → Idx n = {i : Fin n // i ≠ 0}, with [NeZero n]; reason: NeZero n follows from n ≥ 3 and only makes the index 0 available
-- source:
--   Jason Yang, New lower bounds on tensor rank of (n,2,m) matrix multiplication with GPT-6 Astra, STOC 2027 submission (manuscript of October 2026, sha256 6c1df229…), p. 5, Lemma 10

import Mathlib
import Definitions.Def_TensorRankN2M_ThreeTwoM_Decomposition
import Definitions.Def_TensorRankN2M_ThreeTwoM_Normalization
import Definitions.Def_TensorRankN2M_ThreeTwoM_SkewAugmentation
import Definitions.Def_TensorRankN2M_ThreeTwoM_N2M

namespace TensorRankN2M.ThreeTwoM

/-- Lemma 10 (p. 5): for a strongly normalized decomposition of ⟨n,2,m⟩ with `n, m ≥ 3` (under the
standing assumption of §2 that `𝔽` is algebraically closed; §2's other assumption, no `α_r`
constant `0`, is implied by strong normalization),
`ker(Φ) = 0 ⊕ ker(H)`. -/
theorem lemma_10 {𝔽 : Type*} [Field 𝔽] [IsAlgClosed 𝔽] {n m R : ℕ} [NeZero n]
    (hn : 3 ≤ n) (hm : 3 ≤ m) (d : Decomposition 𝔽 n 2 m R)
    (hd : d.StronglyNormalized) :
    LinearMap.ker d.Φ = (⊥ : Submodule 𝔽 (Idx n → U 𝔽 m)).prod (LinearMap.ker d.H) := by sorry

end TensorRankN2M.ThreeTwoM
