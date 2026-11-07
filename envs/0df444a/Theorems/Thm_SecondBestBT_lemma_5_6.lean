-- Prove2me | Theorems.Thm_SecondBestBT_lemma_5_6
-- name    : SecondBestBT.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:45:25.040359+00:00
-- url     : https://prove2.me/theorems/67b7b79a-f0e3-4cba-a974-f363173cc166
-- title:
--   Lemma 5.6 — the constant-virtual-value family and the Gamma limit $\sup_\alpha L(\alpha)=2$
-- statement:
--   For $\alpha>0$, let $G^{(N)}_{N-1}$ be the normalized allocation level of the constant-$\varphi^\alpha_S$ family on $\{0,\dots,N-1\}$ with ratio parameter $r=0$. Then the sequence $(G^{(N)}_{N-1})_{N\ge2}$ is strictly increasing in $N$, and
--   $$
--   \lim_{N\to\infty}G^{(N)}_{N-1}=L(\alpha):=\frac{1}{1+\alpha}\frac{\Gamma\big(\frac1{1+\alpha}\big)^2}{\Gamma\big(\frac2{1+\alpha}\big)} .
--   $$
--   Moreover
--   $$
--   \sup_{\alpha>0}L(\alpha)=2,
--   $$
--   the supremum is not attained at any finite $\alpha$ ($L(\alpha)<2$ for every $\alpha>0$), and it is approached as $\alpha\to\infty$.
--
--   The value $2$ is what makes the target $\beta=1/2$ work: the extremal threshold-zero allocation $x_b=\beta G_b$ stays below one.
--
--   Differences from the source:
--   - encoding: $G^{(N)}_b$ at $r=0$ defined as the limit $r\to0^+$ → the direct value of Eq. (6) at $r=0$; reason: only $r_1,\dots,r_{b-1}$ enter, each continuous and positive at $r=0$ for $b<N$, as the paper notes
--   - encoding: $\sup_{\alpha>0}L(\alpha)=2$, not attained, approached as $\alpha\to\infty$ → `IsLUB` of the image of $(0,\infty)$, $L(\alpha)<2$ for all $\alpha>0$, and $L(\alpha)\to2$ as $\alpha\to\infty$; reason: the three printed claims
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Lemma 5.6, p.20

import Mathlib
import Definitions.Def_SecondBestBT_Gnorm
import Definitions.Def_SecondBestBT_constP
import Definitions.Def_SecondBestBT_gammaLimit

open Filter Topology

namespace SecondBestBT

/-- **Lemma 5.6** (Liu–Qin–Ren–Wang, *Second-Best Bilateral Trade is 1/2 Efficient*,
arXiv:2606.03849, held version sha256 17184930…, Lemma 5.6, p.20). For the constant-`φ^α_S`
family with ratio parameter `r = 0` and `α > 0`, the sequence `(G^{(N)}_{N−1})_{N ≥ 2}` is
strictly increasing in `N`, and
`lim_{N→∞} G^{(N)}_{N−1} = L(α) := (1/(1 + α)) Γ(1/(1 + α))² / Γ(2/(1 + α))`.
Moreover `sup_{α > 0} L(α) = 2`; the supremum is not attained at any finite `α` and is
approached as `α → ∞`.

**Formalization Note** `G^{(N)}_{N−1} = Gnorm α (constP α N) (N − 1)`, with the `r = 0` value
evaluated directly (see `constP`). The supremum is `IsLUB`; "not attained" is `L(α) < 2` for
every `α > 0`; "approached as `α → ∞`" is the limit along `atTop`. -/
theorem lemma_5_6 :
    (∀ α : ℝ, 0 < α →
      StrictMonoOn (fun N : ℕ => Gnorm α (constP α N) (N - 1)) {N | 2 ≤ N} ∧
      Tendsto (fun N : ℕ => Gnorm α (constP α N) (N - 1)) atTop (𝓝 (gammaLimit α))) ∧
    IsLUB (gammaLimit '' Set.Ioi 0) 2 ∧ (∀ α : ℝ, 0 < α → gammaLimit α < 2) ∧
    Tendsto gammaLimit atTop (𝓝 2) := by sorry

end SecondBestBT
