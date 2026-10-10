-- Prove2me | Theorems.Thm_PowerOfDUniversality_Fluid_proposition_3_6
-- name    : PowerOfDUniversality.Fluid.proposition_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:39:34.550642+00:00
-- url     : https://prove2.me/theorems/e8bb8cc3-eea6-49ba-b5c6-ba333a346291
-- title:
--   Proposition 3.6 — P(Δ(T) ≥ M | A(T)) ≤ (A(T)/M)(1 − n/N)^d for JSQ(d) versus JSQ(n, d)
-- statement:
--   Fix $N\ge 1$ servers, a buffer $b\ge 1$, an arrival rate $\lambda\ge 0$, and integers $n,d$ with $0\le n\le N$ and $1\le d\le N$. Two S-coupled systems run JSQ($d$) and JSQ($n,d$). Let $A(T)$ be the number of arrivals in $[0,T]$ and $\Delta(T)$ the number of arrival epochs in $[0,T]$ at which the two systems differ in decision. Then for every $T\ge 0$ and every $M>0$,
--   $$\mathbb P\big(\Delta(T)\ge M\ \big|\ A(T)\big)\le\frac{A(T)}{M}\Big(1-\frac nN\Big)^{d}.$$
--
--   Together with Proposition 3.5 this shows that JSQ($d$) and JSQ($n,d$) are close when $d$ is large compared with $N/n$.
--
--   **Formalization Note** Since $A(T)$ is integer valued, the conditional probability is stated through its values: for every $a\in\mathbb N$, $\mathbb P(\Delta(T)\ge M,\ A(T)=a)\le\frac aM(1-\frac nN)^d\,\mathbb P(A(T)=a)$. The servers are sampled without replacement; the constant $(1-n/N)^d$ of the paper is kept.
-- source:
--   Mukherjee, Borst, van Leeuwaarden & Whiting, Universality of Power-of-d Load Balancing in Many-Server Systems, arXiv:1612.00723v2, p. 15, Proposition 3.6, (3.12)

import Mathlib
import Definitions.Def_PowerOfDUniversality_Fluid_Model
import Definitions.Def_PowerOfDUniversality_Fluid_FluidSpace

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Fluid

/-- **Proposition 3.6** (p. 15, binomial bound for JSQ(d) versus JSQ(n, d)). Two S-coupled
systems (`N ≥ 1` servers, buffer `b ≥ 1`, rate `λ ≥ 0`) run JSQ(d) and JSQ(n, d), with
`1 ≤ d ≤ N` and `n ≤ N`. Let `A(T)` be the number of arrivals and `Δ(T)` the number of times the
two systems differ in decision up to time `T`. For every `T ≥ 0` and `M > 0`,
`P(Δ(T) ≥ M | A(T)) ≤ (A(T)/M) (1 − n/N)^d`, stated for the discrete conditioning variable
`A(T)` as: for every `a ∈ ℕ`, `P(Δ(T) ≥ M, A(T) = a) ≤ (a/M)(1 − n/N)^d · P(A(T) = a)`. -/
theorem proposition_3_6 (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (hb : 1 ≤ b) (lam : ℝ) (hlam : 0 ≤ lam)
    (n d : ℕ) (hn : n ≤ N) (hd1 : 1 ≤ d) (hdN : d ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (sys₁ sys₂ : System P N b lam) (hξ : sys₁.ξ = sys₂.ξ)
    (T : ℝ) (hT : 0 ≤ T) (M : ℝ) (hM : 0 < M) (a : ℕ) :
    P {ω | M ≤ (sys₁.diffDecisions sys₂ (jsqd N d) (jsqnd N n d) ω T : ℝ) ∧
        sys₁.arrivals ω T = a}
      ≤ ENNReal.ofReal ((a : ℝ) / M * (1 - (n : ℝ) / N) ^ d) * P {ω | sys₁.arrivals ω T = a} := by sorry

end PowerOfDUniversality.Fluid
