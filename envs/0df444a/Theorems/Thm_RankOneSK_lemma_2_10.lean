-- Prove2me | Theorems.Thm_RankOneSK_lemma_2_10
-- name    : RankOneSK.lemma_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:30:31.673625+00:00
-- url     : https://prove2.me/theorems/2d71dbcb-d18e-4578-be83-b74f2622e4fc
-- title:
--   Lemma 2.10 — GOE eigenvector delocalization: w.h.p. $z^\top(2\beta I-J)z\ge\frac{\pi\beta\rho}{6.1(\beta+\rho)}\delta^3\|z\|_2^2-\rho\|z\|^2_{\le\delta n}$ for all $z$
-- statement:
--   Let $\delta\in(0,1)$, $\rho,\beta>0$, and let $J$ be an $n\times n$ β-GOE matrix. Let $\|z\|^2_{\le\delta n}$ be the sum of the $\lfloor\delta n\rfloor$ smallest squared coordinates of $z$.
--
--   **Lemma 2.10.** With probability tending to $1$ as $n\to\infty$, simultaneously for all $z\in\mathbb R^n$,
--   $$z^\top(2\beta I-J)z\ \ge\ \frac{\pi\beta\rho}{6.1(\beta+\rho)}\,\delta^3\,\|z\|_2^2-\rho\,\|z\|^2_{\le\delta n}.$$
--
--   A vector whose Rayleigh quotient is close to the top of the spectrum $\lambda_{\max}(J)\approx2\beta$ must spread its mass over every $\delta n$ coordinates. In the proof of Theorem 1.5 it is applied to the vector $w$ of Lemma 3.2, with $1-\delta$ in place of $\delta$.
--
--   Differences from the source:
--   - encoding: with high probability (for sufficiently large n) → the probability of the event tends to 1 as n → ∞, for fixed parameters; reason: the meaning of "with high probability"
--   - encoding: zᵀ(2βI − J)z, ∥z∥₂², constant 6.1 → double sums Σ_i Σ_k z_i (2β δ_ik − J_ik) z_k and Σ z_i², constant 61/10; reason: same quantities
--   - encoding: ∥z∥²_{⩽δn} → smallSumSq z (δ n); reason: same quantity for δ ∈ (0, 1)
--   - encoding: J β-GOE: symmetric, J_ij iid N(0, β²/n) for i < j, J_ii = 0 → the published OAI.SKGap.disorderLaw β n on the entries above the diagonal, with coupling J the full symmetric zero-diagonal matrix; reason: the same law
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, Lemma 2.10, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_RankOneSK_smallSumSq

open OAI.SKGap MeasureTheory ProbabilityTheory Filter Real

namespace RankOneSK

/-- **Lemma 2.10 (GOE eigenvector delocalization).** Let `δ ∈ (0, 1)` and `ρ, β > 0`. Suppose `J` is
β-GOE. Then with high probability, for all `z ∈ ℝⁿ`,
`zᵀ(2βI − J)z ⩾ (πβρ/(6.1(β + ρ)))δ³·∥z∥₂² − ρ∥z∥²_{⩽δn}`.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, Lemma 2.10, p.15.

**Formalization Note** Spins are `OAI.SKGap.Spin n = Fin n → Bool` (±1 through `spinValue`), sites 0-based `Fin n`.
The β-GOE matrix `J` is the published `OAI.SKGap.Disorder n` under `disorderLaw β n`: entries
`J_ik`, `i < k`, i.i.d. `N(0, β²/n)`, `coupling J` symmetric with zero diagonal. "With high probability" is `Tendsto (fun n => disorderLaw β n {event}) atTop (nhds 1)` for each
fixed value of the parameters. `∀ z` is inside the event; `δ, ρ, β` are fixed before
`n`. `zᵀ(2βI − J)z` and `∥z∥₂²` are written as sums; `∥z∥²_{⩽δn}` is `smallSumSq z (δ n)`. The constant
`6.1` is as printed. -/
theorem lemma_2_10 (δ ρ β : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hρ : 0 < ρ) (hβ : 0 < β) :
    Tendsto (fun n : ℕ => disorderLaw β n {J | ∀ z : Fin n → ℝ,
        π * β * ρ / (61 / 10 * (β + ρ)) * δ ^ 3 * (∑ i, z i ^ 2) - ρ * smallSumSq z (δ * n) ≤
          ∑ i : Fin n, ∑ k : Fin n, z i * ((if i = k then 2 * β else 0) - coupling J i k) * z k})
      atTop (nhds 1) := by sorry

end RankOneSK
