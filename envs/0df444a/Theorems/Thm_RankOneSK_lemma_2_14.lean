-- Prove2me | Theorems.Thm_RankOneSK_lemma_2_14
-- name    : RankOneSK.lemma_2_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:28:38.000418+00:00
-- url     : https://prove2.me/theorems/c567cce4-f707-4c81-a2cc-ae3ade6ecab9
-- title:
--   Lemma 2.14 — typical large local fields: w.h.p. for all $x$, fewer than $\delta n$ sites have $|H_i(x)|\le\beta\Phi^{-1}(\frac{1+\delta^\prime}2)$
-- statement:
--   Let $\beta>0$, let $J$ be an $n\times n$ β-GOE matrix, let $h\in\mathbb R^n$ be an external field and $H_i(x)=h_i+\sum_{j\neq i}J_{ij}x_j$ the local field at site $i$. Let $\Phi$ be the standard normal distribution function.
--
--   **Lemma 2.14.** Suppose $0<\delta'<\delta<1$ satisfy
--   $$D_{\mathrm{KL}}\big(\mathrm{Ber}(\delta)\,\|\,\mathrm{Ber}(\delta')\big)=\delta\log\frac{\delta}{\delta'}+(1-\delta)\log\frac{1-\delta}{1-\delta'}>\ln2.\tag{19}$$
--   Then for every choice of fields $h=h^{(n)}\in\mathbb R^n$, with probability tending to $1$ as $n\to\infty$, simultaneously for all $x\in\{\pm1\}^n$,
--   $$\Big|\Big\{i:\ |H_i(x)|\le\beta\,\Phi^{-1}\Big(\frac{1+\delta'}2\Big)\Big\}\Big|<\delta n .$$
--
--   In the proof of Theorem 1.5 this guarantees that, for every configuration, all but $\delta n$ sites have conditional magnetization $|\bar X_i|=|\tanh H_i|$ bounded away from $0$.
--
--   Differences from the source:
--   - encoding: h ∈ ℝⁿ arbitrary → an arbitrary sequence h : (n : ℕ) → Fin n → ℝ; reason: the probability depends on n; convergence for every sequence of fields is the same as convergence uniformly in h
--   - encoding: Φ⁻¹((1 + δ′)/2) → a binder q with cdf (gaussianReal 0 1) q = (1 + δ′)/2; reason: Φ is a continuous increasing bijection onto (0, 1), so q exists and is unique
--   - encoding: D_KL(Ber(δ) ∥ Ber(δ′)) → δ log(δ/δ′) + (1 − δ) log((1 − δ)/(1 − δ′)); reason: the definition; all arguments are positive
--   - encoding: H_i(x) = h_i + Σ_{j≠i} J_ij x_j → h_i + Σ_j coupling J i j · x_j; reason: the diagonal of J is zero
--   - encoding: with high probability (for sufficiently large n) → the probability of the event tends to 1 as n → ∞, for fixed parameters; reason: the meaning of "with high probability"
--   - encoding: J β-GOE: symmetric, J_ij iid N(0, β²/n) for i < j, J_ii = 0 → the published OAI.SKGap.disorderLaw β n on the entries above the diagonal, with coupling J the full symmetric zero-diagonal matrix; reason: the same law
--   - encoding: x ∈ {±1}ⁿ, sites i ∈ [n] → configurations Fin n → Bool read as ±1 by spinValue, sites indexed from 0; reason: Lean convention; same objects
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, Lemma 2.14 and (19), p.17 (PDF p.18)

import Mathlib
import Definitions.Def_SKHighTemperature

open OAI.SKGap MeasureTheory ProbabilityTheory Filter

namespace RankOneSK

/-- **Lemma 2.14 (Typical large local fields).** Let `β > 0` and `J ∈ ℝ^{n×n}` be β-GOE. Suppose
`0 < δ′ < δ < 1` is such that `D_KL(Ber(δ) ∥ Ber(δ′)) > ln 2` (19). Let `h ∈ ℝⁿ` be arbitrary. With high
probability, for all `x ∈ {±1}ⁿ`, `|{i : |H_i(x)| ⩽ βΦ⁻¹((1 + δ′)/2)}| < δn`, where
`H_i(x) = h_i + Σ_{j≠i} J_ij x_j` is the local field.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, Lemma 2.14 and (19), p.17; `H_i` defined on p.17.

**Formalization Note** Spins are `OAI.SKGap.Spin n = Fin n → Bool` (±1 through `spinValue`), sites 0-based `Fin n`.
The β-GOE matrix `J` is the published `OAI.SKGap.Disorder n` under `disorderLaw β n`: entries
`J_ik`, `i < k`, i.i.d. `N(0, β²/n)`, `coupling J` symmetric with zero diagonal. "With high probability" is `Tendsto (fun n => disorderLaw β n {event}) atTop (nhds 1)` for each
fixed value of the parameters. The field `h` may vary with `n`: it is any sequence
`h : (n : ℕ) → Fin n → ℝ`. The quantifier `∀ x` is inside the event. `D_KL(Ber(δ) ∥ Ber(δ′))` is written
`δ log(δ/δ′) + (1 − δ) log((1 − δ)/(1 − δ′))`. `Φ⁻¹((1 + δ′)/2)` is the binder `q` with
`Φ(q) = (1 + δ′)/2`, `Φ` the standard normal CDF `cdf (gaussianReal 0 1)` (it exists and is unique as Φ
is a continuous increasing bijection onto `(0, 1)`). The diagonal of `coupling J` is zero, so the
sum over all `k` is the sum over `k ≠ i`. -/
theorem lemma_2_14 (β δ δ' q : ℝ) (hβ : 0 < β) (hδ' : 0 < δ') (hδδ' : δ' < δ) (hδ : δ < 1)
    (hKL : Real.log 2 < δ * Real.log (δ / δ') + (1 - δ) * Real.log ((1 - δ) / (1 - δ')))
    (hq : cdf (gaussianReal 0 1) q = (1 + δ') / 2) (h : (n : ℕ) → Fin n → ℝ) :
    Tendsto (fun n : ℕ => disorderLaw β n {J | ∀ x : Spin n,
        (((Finset.univ.filter fun i : Fin n =>
            |h n i + ∑ k : Fin n, coupling J i k * spinValue (x k)| ≤ β * q).card : ℕ) : ℝ) <
          δ * n})
      atTop (nhds 1) := by sorry

end RankOneSK
