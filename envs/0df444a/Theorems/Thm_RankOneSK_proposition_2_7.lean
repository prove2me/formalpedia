-- Prove2me | Theorems.Thm_RankOneSK_proposition_2_7
-- name    : RankOneSK.proposition_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:28:35.64897+00:00
-- url     : https://prove2.me/theorems/9a106918-15d0-47d9-917a-9f3ecf2f1db0
-- title:
--   Proposition 2.7 — $\|J\|_{\mathrm{op}}\to2\beta$ in probability for a β-GOE matrix
-- statement:
--   Let $\beta>0$ and let $J$ be an $n\times n$ β-GOE matrix.
--
--   **Proposition 2.7** (Bai–Yin). $\|J\|_{\mathrm{op}}\to2\beta$ in probability: for every $t>0$,
--   $$\Pr\big[\,\big|\|J\|_{\mathrm{op}}-2\beta\big|>t\,\big]\xrightarrow[n\to\infty]{}0 .$$
--
--   Both directions are used in the proof of Theorem 1.5: the upper bound in Case 1 and in (27), the lower bound through the coefficient $s(2-s)\|J\|_{\mathrm{op}}$ of $\mathcal D(f)$.
--
--   Differences from the source:
--   - encoding: convergence in probability → for every t > 0, the probability that the deviation exceeds t tends to 0; reason: the definition of convergence in probability
--   - encoding: ∥J∥_op → ℓ²-operator norm of the matrix (coupling J i k) (the published LiqPremiaEq.opNorm); reason: same quantity
--   - encoding: J β-GOE: symmetric, J_ij iid N(0, β²/n) for i < j, J_ii = 0 → the published OAI.SKGap.disorderLaw β n on the entries above the diagonal, with coupling J the full symmetric zero-diagonal matrix; reason: the same law
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, Proposition 2.7, p.14 (PDF p.15), citing [BY88]

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_LiqPremiaEq_opNorm

open OAI.SKGap MeasureTheory ProbabilityTheory Filter

namespace RankOneSK

/-- **Proposition 2.7 ([BY88]).** Let `β > 0` and let `J` be β-GOE. Then `∥J∥_op → 2β` in probability.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, Proposition 2.7, p.14.

**Formalization Note** Spins are `OAI.SKGap.Spin n = Fin n → Bool` (±1 through `spinValue`), sites 0-based `Fin n`.
The β-GOE matrix `J` is the published `OAI.SKGap.Disorder n` under `disorderLaw β n`: entries
`J_ik`, `i < k`, i.i.d. `N(0, β²/n)`, `coupling J` symmetric with zero diagonal. "→ in probability" is: for every `t > 0`, the probability that the deviation exceeds `t` tends to `0`. `∥J∥_op` is the `ℓ²` operator norm (the published
`LiqPremiaEq.opNorm`) of the matrix `(coupling J i k)`; convergence is two-sided. -/
theorem proposition_2_7 (β : ℝ) (hβ : 0 < β) :
    ∀ t : ℝ, 0 < t →
      Tendsto (fun n : ℕ => disorderLaw β n
          {J | t < |LiqPremiaEq.opNorm (Matrix.of fun i k : Fin n => coupling J i k) - 2 * β|})
        atTop (nhds 0) := by sorry

end RankOneSK
