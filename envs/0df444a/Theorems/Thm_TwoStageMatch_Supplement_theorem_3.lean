-- Prove2me | Theorems.Thm_TwoStageMatch_Supplement_theorem_3
-- name    : TwoStageMatch.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:12:55.389921+00:00
-- url     : https://prove2.me/theorems/06928aee-b58e-468c-ae41-e6d0702f8276
-- title:
--   Theorem 3: Algorithm 2 is $(1-1/e+1/e^2)$-competitive (unweighted, $\lambda=1/(e-1)$) and $0.7613$-competitive (weighted, $\lambda=0.7$) against the optimum online
-- statement:
--   Fix a differentiable, monotone increasing and strictly convex $g:\mathbb R\to\mathbb R$ for the Algorithm 1 branch of Algorithm 2 (Hedge-and-Greed).
--
--   1. **Unweighted supplies.** On every instance with $w_j=1$ for all $j\in S$, every run of Algorithm 2 with $\lambda=1/(e-1)$ satisfies
--   $$\mathbb E\Big[\sum_{j\in S}w_j\mathbb 1\{j\text{ matched in }M_1\cup M_2\}\Big]\ \ge\ \Big(1-\frac1e+\frac1{e^2}\Big)\mathrm{OPT}_{\mathrm{online}},$$
--   so $\Gamma_{\text{matching}}(\text{Algorithm 2},\mathrm{OPT}_{\mathrm{online}})\ge1-1/e+1/e^2\approx0.7674$.
--   2. **Weighted supplies.** On every instance with $w_j>0$ for all $j$, every run of Algorithm 2 with $\lambda=0.7$ satisfies
--   $$\mathbb E\Big[\sum_{j\in S}w_j\mathbb 1\{j\text{ matched in }M_1\cup M_2\}\Big]\ \ge\ 0.7613\cdot\mathrm{OPT}_{\mathrm{online}},$$
--   so $\Gamma_{\text{weighted-matching}}(\text{Algorithm 2},\mathrm{OPT}_{\mathrm{online}})\ge0.7613$.
--
--   Both constants exceed the $3/4$ that Algorithm 1 alone guarantees (Theorem 1), so hedging between the balanced matching and the greedy matroid solution beats $3/4$ against the optimum online.
--
--   Differences from the source:
--   - encoding: Γ(Algorithm 2, OPT_online) ≥ c, a minimum of ALG/OPT over instances → ALG ≥ c · OPT_online on every instance, for every run; reason: the minimum over instances with OPT > 0 is at least c iff every such instance has ALG ≥ c · OPT, and the inequality is trivial when OPT = 0; every run covers every choice of x*, rounding, T̄ and M₁
--   - reading: the greedy-style algorithm of Proposition 3 returns T̄ with guarantee (1 − 1/e − ε) → T̄ ∈ B̄ is any set meeting the guarantee with constant 1 − 1/e; reason: the proof of Proposition 4 uses the constant 1 − 1/e exactly (eq. (13), p.21); an exact maximizer of (9) qualifies
--   - reading: Algorithm 1 run 'for any increasing strictly convex function g' (Algorithm 2, step 3) → g differentiable, monotone and strictly convex; reason: Algorithm 1's program 𝒫^g is defined for differentiable, increasing, strictly convex g (p.12)
--   - encoding: weighted case over weights w_j ≥ 0 → w_j > 0 for every j in clause (b); reason: Algorithm 2 runs Algorithm 1, whose program 𝒫^g divides by w_j and is undefined when some w_j = 0; only those instances are excluded
-- source:
--   Feng, Niazadeh & Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1, Theorem 3, p.18; Algorithm 2, p.19; proof pp.19–24 and §EC.6.2

import Mathlib
import Definitions.Def_TwoStageMatch_Supplement_Algorithm2

universe u

namespace TwoStageMatch.Supplement

/-- **Theorem 3** (Feng, Niazadeh & Saberi, arXiv:2210.11648v1, p.18; proof pp.19–24 and
§EC.6.2). For unweighted supply vertices, Algorithm 2 with `λ = 1/(e − 1)` is
`(1 − 1/e + 1/e²)`-competitive against the optimum online, i.e.
`Γ_matching(Algorithm 2, OPT_online) ≥ 1 − 1/e + 1/e² ≈ 0.7674`. For the weighted case, Algorithm 2
with `λ = 0.7` is `0.7613`-competitive against the optimum online, i.e.
`Γ_weighted-matching(Algorithm 2, OPT_online) ≥ 0.7613`.

Fix any differentiable, monotone increasing and strictly convex `g` (the function used by the
Algorithm 1 branch).
* (a) On every instance with `w_j = 1` for all `j`, every run of Algorithm 2 has
  `value(λ = 1/(e − 1)) ≥ (1 − 1/e + 1/e²) · OPT_online`.
* (b) On every instance with `w_j > 0` for all `j`, every run of Algorithm 2 has
  `value(λ = 0.7) ≥ 0.7613 · OPT_online`.

**Formalization Note.** The competitive ratio `Γ` of Definition 2 is a minimum of `ALG / OPT`
over instances; it is stated per instance (`ALG ≥ c · OPT` on every instance, which is `Γ ≥ c`
over the instances with `OPT > 0` and is trivial when `OPT = 0`), for every run. Clause (b)
assumes positive weights: Algorithm 2 runs Algorithm 1, whose program `𝒫^g` divides by `w_j`
and is undefined when some `w_j = 0`. -/
theorem theorem_3 (g : ℝ → ℝ) (hgd : Differentiable ℝ g) (hgm : Monotone g)
    (hgc : StrictConvexOn ℝ Set.univ g) :
    (∀ {D₁ D₂ S : Type u} [Fintype D₁] [Fintype D₂] [Fintype S]
      [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S] (I : Instance D₁ D₂ S),
        (∀ j, I.w j = 1) → ∀ r : Run2 I g,
          (1 - 1 / Real.exp 1 + 1 / Real.exp 1 ^ 2) * optOnline I ≤
            r.value (1 / (Real.exp 1 - 1))) ∧
    (∀ {D₁ D₂ S : Type u} [Fintype D₁] [Fintype D₂] [Fintype S]
      [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S] (I : Instance D₁ D₂ S),
        (∀ j, 0 < I.w j) → ∀ r : Run2 I g,
          (0.7613 : ℝ) * optOnline I ≤ r.value (7 / 10)) := by sorry

end TwoStageMatch.Supplement
