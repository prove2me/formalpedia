-- Prove2me | Theorems.Thm_TwoStageMatch_Supplement_theorem_ec4
-- name    : TwoStageMatch.Supplement.theorem_ec4
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:16:06.112624+00:00
-- url     : https://prove2.me/theorems/b5ee98a7-4cc0-41a6-834e-54d366b66042
-- title:
--   Theorem EC.4: in single-stage matching and pricing, Algorithm 3 is $(1-1/e)$-competitive against $\mathcal P^{\mathrm{EAR}}$ (corrected: atomless value laws with finite mean)
-- statement:
--   Consider single-stage joint matching and pricing for demand efficiency: no first-stage demands ($D_1=\varnothing$), all supply weights $0$, and independent values $v_i\sim F_i$ on $[0,\infty)$ of the demands $i\in D_2$, each $F_i$ atomless with finite mean. Every run of Algorithm 3, with optimal solution $x$ of $\mathcal P^{\mathrm{EAR}}$, satisfies
--   $$\mathbb E\Big[\sum_{i\in D_2}v_i\mathbb 1\{v_i\ge p_i\text{ and }i\text{ is matched by }M_2\}\Big]\ \ge\ \Big(1-\frac1e\Big)\sum_{i\in D_2}w_i(T_i(y_i))\,y_i,$$
--   the right-hand side being $(1-1/e)$ times the optimal value of the ex ante relaxation $\mathcal P^{\mathrm{EAR}}$. By Lemma 4 the same ratio holds against $\mathrm{OPT}_{\text{offline-MP}}$.
--
--   Without a first stage, posted prices and a maximum-weight matching of the accepting demands lose only the correlation gap of a submodular function.
--
--   Differences from the source:
--   - correction: Lemma 4, Theorem 4 and Theorem EC.4 are stated for arbitrary value laws F_i, with T_i(q) ≜ argmax{t : 1 − F_i(t) ≥ q} and the claim that i accepts the price T_i(y_i) with probability y_i (p.27) → every second-stage law F_i is atomless with finite mean (MPInstance.Regular); reason: for a law with an atom the argmax does not exist and no price is accepted with probability y_i: for a point mass at 1 and any q ∈ (0,1), {t : 1 − F(t) ≥ q} = (−∞, 1) has no maximum and every price is accepted with probability 0 or 1; a finite mean is needed for w_i(p) = E[v | v ≥ p] to be a real number. Excluded: laws with atoms and laws with infinite mean
--   - reading: values v_i ∼ F_i of demands for the service (p.8), never given a sign → each F_i is carried by [0, ∞); reason: a value for the service is a non-negative willingness to pay; the paper's welfare objective, its examples (uniform values, the two-point law on {0, 1/ε}) and its formula w_i(T_i(y))y = ∫_0^y T_i(q)dq all use non-negative values
--   - generalization: price p_i = T_i(y_i) also at y_i = 0, where argmax{t : 1 − F_i(t) ≥ 0} does not exist → the price of a demand with y_i = 0 is arbitrary; reason: the paper's algorithm is undefined there; the Lean statement holds for every choice, so it covers any convention
--   - reading: Algorithm 3 is (1 − 1/e)-competitive (benchmark not named in the statement) → demand efficiency ≥ (1 − 1/e) × the optimal value of 𝒫^EAR; reason: §5 (p.25) and §EC.7 name the ex ante relaxation as the benchmark of this result; by Lemma 4 it implies the ratio against OPT_offline-MP
--   - encoding: single-stage: D₁ empty and all supply weights zero → IsEmpty D₁ and w_j = 0 for every j; the ratio per instance and per run; reason: the same instances; a competitive ratio is this per-instance inequality
-- source:
--   Feng, Niazadeh & Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1, Theorem EC.4, p.ec20; §EC.7, pp.ec19–ec21

import Mathlib
import Definitions.Def_TwoStageMatch_Supplement_Algorithm3

namespace TwoStageMatch.Supplement

/-- **Theorem EC.4** (Feng, Niazadeh & Saberi, arXiv:2210.11648v1, p.ec20; proof pp.ec20–ec21).
In single-stage joint matching and pricing for demand efficiency, Algorithm 3 is
`(1 − 1/e)`-competitive.

Stated against the ex ante relaxation `𝒫^EAR` (the benchmark of §5, p.25, and of §EC.7): on every
single-stage instance (`D₁ = ∅`, all supply weights `0`) whose value laws are atomless with finite
mean, every run of Algorithm 3 has expected demand efficiency at least `(1 − 1/e)` times the
optimal value of `𝒫^EAR`.

**Formalization Note.** `D₁ = ∅` is `IsEmpty D₁`. The optimal value of `𝒫^EAR` is the objective of
the run's own optimal solution `x`. By Lemma 4 the bound also holds against `OPT_offline-MP`. -/
theorem theorem_ec4 {D₁ D₂ S : Type*} [Fintype D₁] [Fintype D₂] [Fintype S] [DecidableEq D₁]
    [DecidableEq D₂] [DecidableEq S] (I : MPInstance D₁ D₂ S) (hI : I.Regular)
    (hD₁ : IsEmpty D₁) (hw : ∀ j, I.w j = 0) (r : Run3 I) :
    (1 - 1 / Real.exp 1) * earObjective I r.x ≤ r.demandEfficiency := by sorry

end TwoStageMatch.Supplement
