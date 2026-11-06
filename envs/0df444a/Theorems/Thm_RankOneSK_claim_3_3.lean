-- Prove2me | Theorems.Thm_RankOneSK_claim_3_3
-- name    : RankOneSK.claim_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:30:47.582282+00:00
-- url     : https://prove2.me/theorems/549c037c-866b-4fda-b15e-50f9c1a9f26d
-- title:
--   Claim 3.3 — $\mathbb E[g(\bar X_i)w_i^2]=\mathbb E[g(\bar X_i)(1-s(2-s)\bar X_i^2)(L_if)^2]$
-- statement:
--   Let $\mu_J$ be the SK Gibbs measure with interaction matrix $J$ (no external field), $L_i=I-P_i$ and $\bar X_i=\bar X_i(x_{-i})$ the conditional magnetization of spin $i$. For $s\in\mathbb R$ and $f:\{\pm1\}^n\to\mathbb R$ let
--   $$w_i(x)=\big(x_i+s\bar X_i(x_{-i})\big)\,L_if(x).$$
--
--   **Claim 3.3.** For every $g:[-1,1]\to\mathbb R$ and every $i\in[n]$,
--   $$\mathbb E_{\mu_J}\big[g(\bar X_i)\,w_i(X)^2\big]=\mathbb E_{\mu_J}\big[g(\bar X_i)\,\big(1-s(2-s)\bar X_i^2\big)(L_if)^2\big].$$
--
--   With $g\equiv1$ and a sum over $i$ it gives $\mathbb E\|w\|_2^2=\mathcal E(f)-s(2-s)\mathcal D(f)$, the last step of Lemma 3.2; with indicator functions it is used again in (30).
--
--   Differences from the source:
--   - encoding: g : [−1, 1] → ℝ → g : ℝ → ℝ; reason: X̄_i takes values in [−1, 1], so only the values of g there enter; every g on [−1, 1] extends
--   - generalization: J the interaction matrix fixed in §3, s the parameter of Lemma 3.2 → every interaction J and every s ∈ ℝ; reason: the claim is an algebraic identity that uses no property of J or s; specializing to the §3 J and s gives the source
--   - encoding: x ∈ {±1}ⁿ, sites i ∈ [n] → configurations Fin n → Bool read as ±1 by spinValue, sites indexed from 0; reason: Lean convention; same objects
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, Claim 3.3, p.20 (PDF p.21)

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_RankOneSK_siteLap
import Definitions.Def_RankOneSK_condMag
import Definitions.Def_RankOneSK_magShift

open OAI.SKGap MeasureTheory ProbabilityTheory Filter

namespace RankOneSK

/-- **Claim 3.3.** Let `w_i(x) = (x_i + sX̄_i(x_{−i}))·L_i f(x)` as in Lemma 3.2 and `g : [−1, 1] → ℝ`. For
`i ∈ [n]`, `E[g(X̄_i) w_i(X)²] = E[g(X̄_i)(1 − s(2 − s)X̄_i²)(L_i f)²]`.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, Claim 3.3, p.20.

**Formalization Note** Spins are `OAI.SKGap.Spin n = Fin n → Bool` (±1 through `spinValue`), sites 0-based `Fin n`.
The β-GOE matrix `J` is the published `OAI.SKGap.Disorder n` under `disorderLaw β n`: entries
`J_ik`, `i < k`, i.i.d. `N(0, β²/n)`, `coupling J` symmetric with zero diagonal. Expectation under the zero-field SK Gibbs measure
`µ_J` (`expectation J 0`). The identity is deterministic: it holds for every interaction `J`, every
`s ∈ ℝ` and every `f`. `g` is taken on all of `ℝ`; since `X̄_i ∈ [−1, 1]`, only its values on `[−1, 1]`
enter. -/
theorem claim_3_3 {n : ℕ} (J : Disorder n) (s : ℝ) (f : Spin n → ℝ) (g : ℝ → ℝ) (i : Fin n) :
    expectation J 0 (fun x => g (condMag J i x) * (magShift J s i x * siteLap J i f x) ^ 2) =
      expectation J 0 (fun x =>
        g (condMag J i x) * (1 - s * (2 - s) * condMag J i x ^ 2) * siteLap J i f x ^ 2) := by sorry

end RankOneSK
