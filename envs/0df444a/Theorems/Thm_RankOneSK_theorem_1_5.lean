-- Prove2me | Theorems.Thm_RankOneSK_theorem_1_5
-- name    : RankOneSK.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:30:40.471198+00:00
-- url     : https://prove2.me/theorems/dd85a0c2-640c-441b-931b-d99e09404d26
-- title:
--   Theorem 1.5 — SK model: w.h.p. $\langle L_Jf,L_Jf\rangle_\mu\ge C\langle L_Jf,f\rangle_\mu$ for all $f$, one $C$ for all $0\le\beta\le\frac12+\varepsilon$, $\varepsilon\ge5\cdot10^{-5}$
-- statement:
--   Let $J$ be an $n\times n$ β-GOE matrix (symmetric, zero diagonal, entries $J_{ij}\sim\mathcal N(0,\beta^2/n)$ independent for $i<j$), and let $\mu=\mu_J$ be the Sherrington–Kirkpatrick Gibbs measure
--   $$\mu_J(x)=\frac1{Z_n}\exp\Big(\frac12x^\top Jx\Big),\qquad x\in\{\pm1\}^n .$$
--   Let $P_if(x)=\mathbb E_\mu[f(X)\mid X_j=x_j\ \forall j\neq i]$, $L_J=\sum_i(I-P_i)$ and $\langle u,v\rangle_\mu=\mathbb E_\mu[uv]$.
--
--   **Theorem 1.5.** There exist an absolute constant $\varepsilon\ge5\cdot10^{-5}$ and a constant $C=C(\varepsilon)>0$ such that for every $\beta$ with $0\le\beta\le\frac12+\varepsilon$,
--   $$\Pr_J\Big[\ \langle L_Jf,L_Jf\rangle_\mu\ \ge\ C\,\langle L_Jf,f\rangle_\mu\ \text{ for every }f:\{\pm1\}^n\to\mathbb R\ \Big]\xrightarrow[n\to\infty]{}1 .$$
--
--   Since $\langle L_Jf,f\rangle_\mu$ is the Dirichlet form $\mathcal E(f)$, this Bochner-type inequality implies (Fact 1.2, Corollary 1.6) a spectral gap $\Omega(1/n)$ for Glauber dynamics and mixing time $O(n^2)$ on the whole range $0\le\beta\le\frac12+\varepsilon$, improving the earlier threshold $\beta\approx0.295$ of Anari, Koehler and Vuong (2024).
--
--   Differences from the source:
--   - encoding: "for sufficiently large n > n₀(β) with high probability … simultaneously for every f" → for each fixed β, the disorderLaw β n-probability of the event {∀ f, …} tends to 1 as n → ∞; reason: meaning of "with high probability"; only n₀ depends on β
--   - encoding: C = C(ε) > 0 → ∃ C > 0 chosen after ε and before β; reason: C depends only on ε
--   - encoding: J β-GOE: symmetric, J_ij iid N(0, β²/n) for i < j, J_ii = 0 → the published OAI.SKGap.disorderLaw β n on the entries above the diagonal, with coupling J the full symmetric zero-diagonal matrix; reason: the same law
--   - encoding: x ∈ {±1}ⁿ, sites i ∈ [n] → configurations Fin n → Bool read as ±1 by spinValue, sites indexed from 0; reason: Lean convention; same objects
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, Theorem 1.5, p.4 (PDF p.5); (4), p.4; β-GOE, p.11; P_i, L_i, ⟨·,·⟩_µ, p.2

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_RankOneSK_lap
import Definitions.Def_RankOneSK_muInner

open OAI.SKGap MeasureTheory ProbabilityTheory Filter

namespace RankOneSK

/-- **Theorem 1.5.** Let `L_J = Σ_i L_i = Σ_i (I − P_i)`. There exists an absolute constant
`ε ⩾ 5·10⁻⁵` with the following property. If `0 ⩽ β ⩽ 1/2 + ε`, then for sufficiently large `n > n₀(β)`
with high probability over the randomness of the interaction matrix `J`, simultaneously for every
`f : {±1}ⁿ → ℝ`, `⟨L_J f, L_J f⟩_µ ⩾ C·⟨L_J f, f⟩_µ`, where `C = C(ε) > 0`.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, Theorem 1.5, p.4; the SK model (4) and β-GOE, p.4 and p.11; `P_i`, `L_i`, `⟨·,·⟩_µ`, p.2.

**Formalization Note** Spins are `OAI.SKGap.Spin n = Fin n → Bool` (±1 through `spinValue`), sites 0-based `Fin n`.
The β-GOE matrix `J` is the published `OAI.SKGap.Disorder n` under `disorderLaw β n`: entries
`J_ik`, `i < k`, i.i.d. `N(0, β²/n)`, `coupling J` symmetric with zero diagonal. "With high probability" is `Tendsto (fun n => disorderLaw β n {event}) atTop (nhds 1)` for each
fixed value of the parameters. `C` is chosen after `ε` and before `β` and `n`: only the
threshold `n₀` (hidden in the limit) depends on `β`. `β = 0` is included. `∀ f` is inside the event. No
external field. -/
theorem theorem_1_5 :
    ∃ ε : ℝ, 5 * 10 ^ (-5 : ℤ) ≤ ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 0 ≤ β → β ≤ 1 / 2 + ε →
      Tendsto (fun n : ℕ => disorderLaw β n
          {J | ∀ f : Spin n → ℝ, C * muInner J (lap J f) f ≤ muInner J (lap J f) (lap J f)})
        atTop (nhds 1) := by sorry

end RankOneSK
