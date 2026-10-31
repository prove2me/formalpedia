-- Prove2me | Theorems.Thm_QueueSignal_lamO_eq_and_strictMono
-- name    : QueueSignal.lamO_eq_and_strictMono
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:06:41.849709+00:00
-- url     : https://prove2.me/theorems/459b5132-9a7a-4b59-8790-ce937986066e
-- title:
--   Eq. (1) — $\lambda^O(d)=\lambda(1-p_{n(d)+1})=\mu-\mu/\sum_{i=0}^{n(d)+1}\rho^i$, strictly increasing in $\lambda$
-- statement:
--   Let $\mu,\theta>0$, $V_H>V_L>\theta/\mu$, $0<\delta<1$, and let $d\in[0,1]$ be the customers' belief after the server reveals its queue. Write $\rho=\lambda/\mu$, $n=n(d)$ for Naor's threshold, and
--   $$p_{n+1}=\frac{\rho^{n+1}}{\sum_{i=0}^{n+1}\rho^i}$$
--   for the probability that the $M/M/1/(n+1)$ queue is full. Then for every potential arrival rate $\lambda>0$,
--   $$\lambda^O(d)=\lambda\,(1-p_{n+1})=\mu-\frac{\mu}{\sum_{i=0}^{n+1}\rho^i},$$
--   and $\lambda\mapsto\lambda^O(d)$ is strictly increasing on $(0,\infty)$.
--
--   The closed form $\mu-\mu/\sum\rho^i$ is what makes the comparison of revealing and concealing tractable: it is continuous and increasing in $\lambda$ and tends to $\mu$.
--
--   **Formalization Note** $\lambda^O$ is defined by the right-hand form of (1); $n(d)$ is an integer converted with `Int.toNat`.
--
--   Differences from the source:
--   - encoding: n(δ^R) = ⌊[δ^R V_H + (1 − δ^R)V_L]µ/θ⌋ − 1 used as a summation bound → computed in ℤ and converted with Int.toNat; reason: under V_L > θ/µ and a belief in [0, 1] it is ≥ 0, so the conversion changes no instance
--   - encoding: λ^O(δ^R) is strictly increasing in the potential arrival rate λ → StrictMonoOn (λ ↦ λ^O(λ, d)) on (0, ∞); reason: λ is a positive rate throughout the paper
-- source:
--   Guo, Haviv, Luo, Wang, Signaling Service Quality Through Queue Disclosure, MSOM 25(2) (2023), doi:10.1287/msom.2022.1170, §4.1, eq. (1) and the remark after it, p.548

import Mathlib
import Definitions.Def_QueueSignal_SignalingGame
import Definitions.Def_QueueSignal_QueueModel

namespace QueueSignal

/-- **(1) and the rewrite after it** (Guo, Haviv, Luo, Wang, *Signaling Service Quality Through Queue Disclosure*, MSOM 25(2) (2023),
doi:10.1287/msom.2022.1170, §4.1, eq. (1), p.548, PDF p.7).

For a belief `d ∈ [0, 1]`, `λ > 0`, `ρ = λ/μ` and `n = n(d)`, with
`p_{n+1} = ρ^{n+1} / Σ_{i=0}^{n+1} ρ^i` the probability that the `M/M/1/(n+1)` queue is full,
`λ^O(d) = λ(1 − p_{n+1}) = μ − μ / Σ_{i=0}^{n+1} ρ^i`;
and `λ ↦ λ^O(d)` is strictly increasing on `(0, ∞)`.

**Formalization Note.** `n(d)` is the `ℤ`-valued `Params.naorN`, nonnegative here, taken as a
natural number with `Int.toNat`. -/
theorem lamO_eq_and_strictMono (P : Params) (hP : P.Valid) (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    (∀ lam : ℝ, 0 < lam →
      lamO P lam d = lam * (1 - (lam / P.μ) ^ ((P.naorN d).toNat + 1) /
          ∑ i ∈ Finset.range ((P.naorN d).toNat + 2), (lam / P.μ) ^ i) ∧
      lamO P lam d = P.μ - P.μ / ∑ i ∈ Finset.range ((P.naorN d).toNat + 2), (lam / P.μ) ^ i) ∧
    StrictMonoOn (fun lam => lamO P lam d) (Set.Ioi 0) := by sorry

end QueueSignal
