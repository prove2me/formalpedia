-- Prove2me | Theorems.Thm_OverbookBL_proposition_2
-- name    : OverbookBL.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:51:16.051301+00:00
-- url     : https://prove2.me/theorems/3aef9df2-7bf3-4140-bee7-8438dadf9ce9
-- title:
--   Proposition 2 — monotonicity of $P[\mathrm{Bin}(n,\lambda/n)\ge m]$ in $n$ (Pinelis, Cor. 4; corrected: $m\le n_2$ in (i), $m\ge1$ in (ii))
-- statement:
--   Let $\lambda>0$, let $n_1<n_2$ be natural numbers with $n_1\ge\lambda$, and let $Y_n\sim\mathrm{Bin}(n,\lambda/n)$.
--
--   1. If $1+\lambda\le m\le n_2$, then $\mathbb P[Y_{n_1}\ge m]<\mathbb P[Y_{n_2}\ge m]$.
--   2. If $1\le m\le\lambda$, then $\mathbb P[Y_{n_1}\ge m]>\mathbb P[Y_{n_2}\ge m]$.
--
--   Among binomial laws with the same mean $\lambda$, more trials make large values more likely and small positive values less likely. The paper uses it to compare $\mathrm{Bin}(R/p_i,p_i)$ and $\mathrm{Bin}(R/p_j,p_j)$ when $q_i=q_j$ (Lemma 4, case (ii)).
--
--   Differences from the source:
--   - correction: (i) if m ≥ 1 + λ then P[Y_{n₁} ≥ m] < P[Y_{n₂} ≥ m] → (i) under 1 + λ ≤ m ≤ n₂; reason: false for m > n₂: λ = 1, m = 3, n₁ = 1, n₂ = 2 gives 0 < 0
--   - correction: (ii) if m ≤ λ then P[Y_{n₁} ≥ m] > P[Y_{n₂} ≥ m] → (ii) under 1 ≤ m ≤ λ; reason: false at m = 0, where both tails are 1
--   - encoding: λ ∈ (0, ∞), n ∈ ℕ, Yₙ ∼ Bin(n, λ/n) → λ ≤ n₁ < n₂; reason: Bin(n, λ/n) is a distribution only for n ≥ λ
-- source:
--   D. Freund and J. Zhao, Overbooking with bounded loss, arXiv:2204.11148v2 (26 Apr 2022), https://arxiv.org/abs/2204.11148v2, Proposition 2, Appendix A.3, p.43 (Corollary 4 in Pinelis 2020)

import Definitions.Def_OverbookBL_showE

namespace OverbookBL

/-- **Proposition 2** (Freund & Zhao, *Overbooking with bounded loss*, arXiv:2204.11148v2,
Appendix A.3, p.43; Corollary 4 in Pinelis 2020), with corrected domain. Take `λ ∈ (0, ∞)`
and natural numbers `λ ≤ n₁ < n₂`, and let `Yₙ ∼ Bin(n, λ/n)`.
(i) If `1 + λ ≤ m ≤ n₂`, then `P[Y_{n₁} ≥ m] < P[Y_{n₂} ≥ m]`.
(ii) If `1 ≤ m ≤ λ`, then `P[Y_{n₁} ≥ m] > P[Y_{n₂} ≥ m]`.

**Formalization Note** As printed ("Take any `λ ∈ (0, ∞)`, `n ∈ ℕ`"; (i) "if `m ≥ 1 + λ`";
(ii) "if `m ≤ λ`") the proposition is false: in (i) `λ = 1, m = 3, n₁ = 1, n₂ = 2` gives
`0 < 0`, and in (ii) `m = 0` gives `1 > 1`. The upper bound `m ≤ n₂` in (i) and the lower bound
`m ≥ 1` in (ii) are the minimal corrections. `n₁ ≥ λ` is needed for `Bin(n, λ/n)` to be a
distribution. Its use in Appendix A.3 (`λ = R`, `n = R/pᵢ < R/pⱼ`) lies inside this domain. -/
theorem proposition_2 (lam : ℝ) (hlam : 0 < lam) (n₁ n₂ : ℕ) (hn₁ : lam ≤ n₁) (h12 : n₁ < n₂) (m : ℕ) : ((1 + lam ≤ m → m ≤ n₂ → binTail n₁ (lam / n₁) m < binTail n₂ (lam / n₂) m) ∧ (1 ≤ m → (m : ℝ) ≤ lam → binTail n₂ (lam / n₂) m < binTail n₁ (lam / n₁) m)) := by sorry

end OverbookBL
