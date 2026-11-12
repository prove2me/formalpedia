-- Prove2me | Theorems.Thm_TensorRankN2M_ThreeTwoM_lemma_12
-- name    : TensorRankN2M.ThreeTwoM.lemma_12
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T04:18:38.684075+00:00
-- url     : https://prove2.me/theorems/251e3a0e-8202-46cd-bed4-aaf35fd5808c
-- title:
--   Lemma 12 — for n = 3, dim(S) ≥ dim(N) − Δ
-- statement:
--   Let $\mathbb F$ be algebraically closed, $m\ge 3$, and let $(\alpha_r,\beta_r,C_r)_{0\le r<R}$ be a strongly normalized $R$-rank decomposition of $\langle 3,2,m\rangle$ over $\mathbb F$. With $L$, $H$ as in §4 ($n=3$), $U^{\wedge 2}\cong U$ via $c_{1,2}=-x$, $c_{2,1}=x$, and
--   $$\Delta=2\operatorname{rk}(H)-\operatorname{rk}(L),\qquad N=\ker(H)\subseteq U,\qquad S=\{x\in N: f_1(x),f_2(x)\in f_0(N)\},$$
--   we have
--   $$\dim(S)\ \ge\ \dim(N)-\Delta .$$
--
--   Together with Lemma 8 this gives $\Delta\ge\min(2,\dim N)$, the case split behind the bound $R(\langle 3,2,m\rangle)\ge\lceil(24m+2)/5\rceil$.
--
--   Differences from the source:
--   - reading: the lemma's sentence carries no hypotheses → 𝔽 algebraically closed, the decomposition strongly normalized, n = 3, m ≥ 3; reason: §2's standing assumptions (p. 2), §3's strong normalization (p. 4), §4's m, n ≥ 3 (p. 4) and §4.1's n = 3 are in force; §2's other assumption, no α_r identically 0, is not a separate hypothesis because strong normalization implies it (D(e_{0,0}) invertible)
--   - encoding: N = ker(H) ⊆ U via U^{∧2} ≅ U → Nspace = ker(H ∘ skewOfU), skewOfU x having c_{1,2} = −x, c_{2,1} = x; reason: this is the identification under which the paper's h(x) = (−f_2(x), f_1(x))
--   - encoding: Δ and the inequality → in ℤ (Delta : ℤ, finrank cast to ℤ); reason: Δ may be negative a priori
--   - encoding: rk(L), rk(H) with codomains ker(W)/J, (ker(W)/J)^2 → ranges with codomains 𝔽^R/J, (𝔽^R/J)^2; reason: the paper's codomains are subspaces, so ranks and kernels are unchanged
-- source:
--   Jason Yang, New lower bounds on tensor rank of (n,2,m) matrix multiplication with GPT-6 Astra, STOC 2027 submission (manuscript of October 2026, sha256 6c1df229…), p. 6, §4.1, Lemma 12

import Mathlib
import Definitions.Def_TensorRankN2M_ThreeTwoM_Decomposition
import Definitions.Def_TensorRankN2M_ThreeTwoM_Normalization
import Definitions.Def_TensorRankN2M_ThreeTwoM_SkewAugmentation
import Definitions.Def_TensorRankN2M_ThreeTwoM_N2M
import Definitions.Def_TensorRankN2M_ThreeTwoM_CaseN3

namespace TensorRankN2M.ThreeTwoM

/-- Lemma 12 (p. 6): for a strongly normalized decomposition of ⟨3,2,m⟩ with `m ≥ 3` (under the
standing assumption of §2 that `𝔽` is algebraically closed; §2's other assumption, no `α_r`
constant `0`, is implied by strong normalization),
`dim(S) ≥ dim(N) − Δ`, where `Δ = 2rk(H) − rk(L)`, `N = ker(H) ⊆ U` and
`S = {x ∈ N : f_1(x), f_2(x) ∈ f_0(N)}`. -/
theorem lemma_12 {𝔽 : Type*} [Field 𝔽] [IsAlgClosed 𝔽] {m R : ℕ} (hm : 3 ≤ m)
    (d : Decomposition 𝔽 3 2 m R) (hd : d.StronglyNormalized) :
    (Module.finrank 𝔽 d.Nspace : ℤ) - d.Delta ≤ Module.finrank 𝔽 d.Sspace := by sorry

end TensorRankN2M.ThreeTwoM
