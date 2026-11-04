-- Prove2me | Theorems.Thm_OverbookBL_claim_1
-- name    : OverbookBL.claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:51:29.066952+00:00
-- url     : https://prove2.me/theorems/8b1c3f7e-b3be-447c-b705-ca45dd84ba94
-- title:
--   Claim 1 — the quantile shift $F_Y^{-1}(\bar q_j)-F_Z^{-1}(\bar q_j)\ge 1$ for $m\ge m_0$
-- statement:
--   Fix a type $j$ and let $\bar q_j=1-v_j/p_j$. There exist constants $\delta^\star_j\ge1$ and $m_0$ such that for every acceptance vector $\vec x$ with $m=\sum_{n=1}^kx_n\ge m_0$,
--
--   $$
--   F_Y^{-1}(\bar q_j)-F_Z^{-1}(\bar q_j)\ge1,\qquad Y=\sum_{n\ne j}X_{n,x_n}+X_{j,x_j+\delta^\star_j},\quad Z=\sum_nX_{n,x_n},
--   $$
--
--   where $F^{-1}$ is the quantile function and $X_{n,y}\sim\mathrm{Bin}(y,p_n)$ are independent.
--
--   Adding a bounded number of type-$j$ customers moves the $\bar q_j$-quantile of the show-ups by at least one, uniformly in the size of the vector. This is the step that makes the constant of Lemma 2 independent of the capacity.
--
--   Differences from the source:
--   - encoding: the model of §2 (p.9) with implicit vⱼ ≥ 0, pⱼ > 0 and the tie rule for adjacent types → the structure Instance with explicit 0 ≤ vⱼ, 0 < pⱼ, and the tie rule for every pair i < j; vⱼ < 1 not a separate field; reason: vⱼ is a revenue and qⱼ = vⱼ/pⱼ must be defined; for sorted ratios the pairwise and adjacent tie rules are equivalent; vⱼ < 1 follows from vⱼ < pⱼ ≤ 1; no instance changes
--   - reading: qⱼ < 1 assumed "without loss of generality" (p.10) → qⱼ < 1 for every type, as a field of Instance; reason: the paper's standing assumption for all its results; the one-sentence reduction for qⱼ ≥ 1 is a remark, not a theorem, and is not formalized
--   - encoding: the quantile function F⁻¹ ("the inverse of CDF", p.12) → lower quantile min{s ∈ ℕ : F(s) ≥ r}; reason: the inverse the proof uses on p.18
--   - encoding: F_Y⁻¹(q̄ⱼ) − F_Z⁻¹(q̄ⱼ) ≥ 1 → F_Z⁻¹(q̄ⱼ) + 1 ≤ F_Y⁻¹(q̄ⱼ) in ℕ; reason: same inequality without subtraction
--   - encoding: m₀ ∈ ℤ⁺ → m₀ ∈ ℕ; reason: a valid m₀ = 0 gives the valid m₀ = 1; no instance changes
-- source:
--   D. Freund and J. Zhao, Overbooking with bounded loss, arXiv:2204.11148v2 (26 Apr 2022), https://arxiv.org/abs/2204.11148v2, Claim 1, p.17 (proof Appendix A.2, pp.39–42)

import Definitions.Def_OverbookBL_Instance
import Definitions.Def_OverbookBL_showE

namespace OverbookBL

/-- **Claim 1** (Freund & Zhao, *Overbooking with bounded loss*, arXiv:2204.11148v2, p.17). For
every type `j` there are constants `δ⋆ⱼ ≥ 1` and `m₀` such that for every acceptance vector `x`
with `m = ∑ₙ xₙ ≥ m₀`, writing `Y = ∑_{n≠j} X_{n,xₙ} + X_{j,xⱼ+δ⋆}` and `Z = ∑ₙ X_{n,xₙ}`,
`F_Y⁻¹(q̄ⱼ) − F_Z⁻¹(q̄ⱼ) ≥ 1`, where `q̄ⱼ = 1 − vⱼ/pⱼ`.

**Formalization Note** `Y` is the show-up count of `x + δ⋆ eⱼ` and `Z` that of `x`. `F⁻¹` is the
lower quantile `min {s ∈ ℕ | F(s) ≥ r}` (`showQuantile`); the difference of quantiles is written
`F_Z⁻¹(q̄ⱼ) + 1 ≤ F_Y⁻¹(q̄ⱼ)` in `ℕ`. -/
theorem claim_1 {k : ℕ} (I : Instance k) (j : Fin k) : ∃ δs : ℕ, 1 ≤ δs ∧ ∃ m₀ : ℕ, ∀ x : Fin k → ℕ, m₀ ≤ ∑ n, x n → showQuantile I.p x (1 - I.v j / I.p j) + 1 ≤ showQuantile I.p (x + δs • Pi.single j 1) (1 - I.v j / I.p j) := by sorry

end OverbookBL
