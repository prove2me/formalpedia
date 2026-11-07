-- Prove2me | Theorems.Thm_VertexSampleCSP_corollary_D_2
-- name    : VertexSampleCSP.corollary_D_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:16.597209+00:00
-- url     : https://prove2.me/theorems/d538d96c-3313-43c7-9154-bdcf13f39ee5
-- title:
--   Corollary D.2, p.18 — tail bound: error $\varepsilon n^r$ with probability $1-\delta$ for $k\ge\max\{r,(2C'_{r,q}/\varepsilon)^2,2\ln(2/\delta)/(\varepsilon^2((r-1)!)^2)\}$
-- statement:
--   Let $\mathcal I$ be an instance of arity $r$ over $[q]$ on $n$ variables with payoffs in $[0,1]$, and let $S$ be a uniformly random $k$-subset.
--
--   1. If $r\le k\le n$, then for every $t>0$,
--
--   $$\mathbb P\Big(\big|\mathrm{OPT}(\mathcal I[S])-\mathbb E\,\mathrm{OPT}(\mathcal I[S])\big|\ge t\binom{k-1}{r-1}\Big)\le2e^{-2t^2/k}.$$
--
--   2. If $0<\varepsilon,\delta<1$ and
--
--   $$\max\Big\{r,\Big(\frac{2C'_{r,q}}{\varepsilon}\Big)^2,\frac{2\ln(2/\delta)}{\varepsilon^2((r-1)!)^2}\Big\}\le k\le n,$$
--
--   then $|(n/k)^r\mathrm{OPT}(\mathcal I[S])-\mathrm{OPT}(\mathcal I)|\le\varepsilon n^r$ with probability at least $1-\delta$.
--
--   The second clause is the high-probability half of the goal theorem with an explicit threshold.
--
--   Differences from the source:
--
--   - encoding: arity r ≥ 2 of the section → hypothesis 2 ≤ r; reason: the standing assumption of Appendix A
--   - encoding: alphabet [q] = {1, …, q} → q ≥ 1 is a hypothesis and the alphabet is Fin q; reason: q = 0 leaves the optimum and the polytopes undefined, so this excludes only undefined cases
--   - encoding: I[S] is the instance on S → I.sub S on the subtype ↥S; reason: same instance, written in a type with |S| variables
--   - encoding: n variables → finite type V with n = |V|; reason: same instances up to the names of the variables
--   - encoding: a uniformly random k-set S → k ≤ |V| in both clauses, with the finite averages unifAvg and unifProb; reason: a k-subset exists only for k ≤ |V|
--   - encoding: ln and "within εn^r" → Real.log and ≤ εn^r; reason: the natural logarithm and the closed reading of "within"
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Corollary D.2, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_VertexSampleCSP_Instance
import Definitions.Def_VertexSampleCSP_OPT
import Definitions.Def_VertexSampleCSP_Instance_sub
import Definitions.Def_VertexSampleCSP_PayoffsIn01
import Definitions.Def_VertexSampleCSP_unifAvg
import Definitions.Def_VertexSampleCSP_Cr

namespace VertexSampleCSP

/-- **Corollary D.2 (Theorem 1.1, tail bound).** Chang, *Optimal Vertex Sampling for Constraint
Satisfaction Problems*, STOC 2027 submission (manuscript sha256 1e0edd23…), Corollary D.2, p.18 (PDF
p.20): "If all payoffs lie in [0, 1] and k ≥ r, then
P(|OPT(I[S]) − E OPT(I[S])| ≥ t·C(k−1, r−1)) ≤ 2e^{−2t²/k} for every t > 0. Consequently, for
0 < ε, δ < 1 and k ≥ max{r, (2C′_{r,q}/ε)², 2 ln(2/δ)/(ε² ((r − 1)!)²)}, the estimate
(n/k)^r OPT(I[S]) is within εn^r of OPT(I) with probability at least 1 − δ."

Here `S` is a uniformly random `k`-subset of the `n` variables and `C(k−1, r−1)` is a binomial
coefficient.
1. If `r ≤ k ≤ n` and `t > 0`:
   `P(|OPT(I[S]) − E OPT(I[S])| ≥ t·C(k−1, r−1)) ≤ 2 e^{−2t²/k}`.
2. If `0 < ε, δ < 1` and `max{r, (2C′_{r,q}/ε)², 2 ln(2/δ)/(ε²((r−1)!)²)} ≤ k ≤ n`:
   `P(|(n/k)^r OPT(I[S]) − OPT(I)| ≤ εn^r) ≥ 1 − δ`.

**Formalization Note.** The `n` variables are a finite type `V` with `n = |V|`; a uniformly random
`k`-set exists only for `k ≤ n`, which both clauses assume. Probabilities and the expectation are the
finite averages over the `k`-subsets. `ln` is `Real.log`. "Within εn^r" is `≤ εn^r`. `I[S]` is the
instance on the subtype `↥S`; `[q]` is `Fin q` with `q ≥ 1`. -/
theorem corollary_D_2 {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ} (hr : 2 ≤ r) (hq : 0 < q)
    (I : Instance V r q) (hI : PayoffsIn01 I) :
    (∀ k : ℕ, r ≤ k → k ≤ Fintype.card V → ∀ t : ℝ, 0 < t →
      unifProb k (fun S => t * ((k - 1).choose (r - 1) : ℝ) ≤
          |OPT (I.sub S) - unifAvg k (fun S' => OPT (I.sub S'))|) ≤
        2 * Real.exp (-2 * t ^ 2 / k)) ∧
    (∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → ∀ k : ℕ, k ≤ Fintype.card V →
      max (max (r : ℝ) ((2 * Crq' r q / ε) ^ 2))
          (2 * Real.log (2 / δ) / (ε ^ 2 * (((r - 1).factorial : ℕ) : ℝ) ^ 2)) ≤ k →
      1 - δ ≤ unifProb k (fun S =>
        |((Fintype.card V : ℝ) / k) ^ r * OPT (I.sub S) - OPT I| ≤
          ε * (Fintype.card V : ℝ) ^ r)) := by sorry

end VertexSampleCSP
