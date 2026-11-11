-- Prove2me | Theorems.Thm_SumReLU_claim_3_9_variance
-- name    : SumReLU.claim_3_9_variance
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:26:37.955345+00:00
-- url     : https://prove2.me/theorems/0135b4fc-0080-4ff6-8ccb-26e414494676
-- title:
--   Claim 3.9, second-moment bound (proof, p.18) — $\mathbb E[y^2\mathrm{he}_p(v\cdot x)^2]\le6k^2p$
-- statement:
--   Let $f(x)=\sum_{i=1}^k\beta_i\sigma(w_i\cdot x)$ with $\beta_i\in[0,1]$ and $\|w_i\|_2=1$, let $v$ be a unit vector and let $p\ge2$ be an integer. With $x\sim N(0,I_d)$ and $y=f(x)$, the random variable $y^2\,\mathrm{he}_p(v\cdot x)^2$ is integrable and
--   $$
--   \mathbb E\big[y^2\,\mathrm{he}_p(v\cdot x)^2\big]\le6k^2p .
--   $$
--
--   This variance bound gives, through Chebyshev's inequality, the sample size of the tester's empirical estimate of $a_p(v)$ (Claim 3.9).
--
--   Differences from the source:
--   - generalization: $p$ the tester's even degree → every integer $p\ge2$; reason: the display uses only $p\ge2$ ("since $p\ge2$"); its even-$p$ case is the printed one
--   - encoding: $\mathbb E[y^2\mathrm{he}_p(v\cdot x)^2]\le6k^2p$ → the integrand is integrable and its integral against $N(0,I_d)$ is at most $6k^2p$, with $y=f(x)$; reason: the expectation presupposes integrability; asserting it keeps the Bochner integral from being a junk $0$
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), proof of Claim 3.9, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_GaussPart_hermiteTensor
import Definitions.Def_SumReLU_reluSum

open MeasureTheory ProbabilityTheory

namespace SumReLU

/-- **Claim 3.9, second-moment bound** (proof of Claim 3.9, p.18).

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), proof of Claim 3.9, p.18 (PDF p.20): "Therefore, by (10), since p ≥ 2, we have:
E[y² he_p(v · x)²] ≤ k ∑_{i=1}^k E_{x∼N}[(cos θ(w_i, v) v · x + sin θ(w_i, v) ŵ_i^{⊥v} · x)² he_p(v · x)²]
≤ … = 2k ∑_{i=1}^k ((2p + 1) + 1) ≤ 6k²p."

**Formalization Note.** `y = f(x)`, `x ∼ N(0, I_d)`, `v` a unit vector. The end-to-end inequality
`E[y² he_p(v·x)²] ≤ 6k²p` is stated, together with the integrability of the integrand (so that the
Bochner integral is not a junk `0`). -/
theorem claim_3_9_variance {d k : ℕ} (β : Fin k → ℝ) (w : Fin k → EuclideanSpace ℝ (Fin d))
    (hf : InClass β w) (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) (p : ℕ) (hp : 2 ≤ p) :
    Integrable (fun x => reluSum β w x ^ 2 * GaussPart.hermiteOne p (inner ℝ v x) ^ 2)
        (stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
      ∫ x, reluSum β w x ^ 2 * GaussPart.hermiteOne p (inner ℝ v x) ^ 2
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ 6 * (k : ℝ) ^ 2 * p := by sorry

end SumReLU
