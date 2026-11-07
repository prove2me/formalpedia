-- Prove2me | Theorems.Thm_PlantedIQP_lemma_35
-- name    : PlantedIQP.lemma_35
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:23:37.877307+00:00
-- url     : https://prove2.me/theorems/7b72f888-a6ff-4bce-a7c4-1d5707f81b5d
-- title:
--   Lemma 35 — the ideal sampler passes with probability $\ge 1-10/L$
-- statement:
--   Let $D$ be any distribution on cubic polynomials, $n\ge1$, $L\ge1$ and $\ell\ge1$. Draw $f_1,\dots,f_L\leftarrow M(n)$ independently and, for each $j$, $\ell$ independent samples $x^{f_j}_1,\dots,x^{f_j}_\ell$ from the ideal law $p_{f_j}$. Then
--
--   $$
--   \Pr\big[\hat\chi\ge1\big]\ \ge\ 1-\frac{10}{L}.
--   $$
--
--   This is the completeness of the XEB test for an ideal (noiseless) quantum sampler.
--
--   Differences from the source:
--   - generalization: ℓ = 1 → every ℓ ≥ 1; reason: more samples per polynomial do not increase the variance of χ̂ (law of total variance), and ℓ = 1 is the special case
--   - reading: with probability at least 1 − 10/L → for every n ≥ 1, L ≥ 1 and every cubic-part law D of M(n), f_j i.i.d. from M(n) and samples i.i.d. from p_{f_j}; reason: the lemma is stated in the setting of Section 3.2 without restrictions on n, L or D; at n = 0 the test fails surely
-- source:
--   Bläser, Gullans, Hangleiter, Liu, Qiao, Verifiable quantum advantage based on polynomials with planted structures, arXiv:2609.39918 (sha256 6e261694…), Lemma 35, p.23

import Mathlib
import Definitions.Def_PlantedIQP_xebHat
import Definitions.Def_PlantedIQP_distributions

set_option autoImplicit false

namespace PlantedIQP

/-- Bläser, Gullans, Hangleiter, Liu, Qiao, *Verifiable quantum advantage based on polynomials with
planted structures*, arXiv:2609.39918 (sha256 6e261694…), Lemma 35, p.23 (completeness for the ideal sampler): for `q_f = p_f`,
`χ̂ ≥ 1` with probability at least `1 − 10/L`. Stated for `f_1, …, f_L ← M(n)` independent (any cubic-part
law `D`), `ℓ` independent samples from `p_{f_j}` per polynomial, every `n ≥ 1`, `L ≥ 1` and every
`ℓ ≥ 1` (the source states `ℓ = 1`). -/
theorem lemma_35 (n L ℓ : ℕ) (hn : 1 ≤ n) (hL : 1 ≤ L) (hℓ : 1 ≤ ℓ) (D : PMF (CubicPoly n)) :
    1 - 10 / (L : ℝ) ≤ tupleProb n L ℓ (mixM D) pf (fun f x => Passes f x) := by sorry

end PlantedIQP
