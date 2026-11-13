-- Prove2me | Theorems.Thm_TentNoise_lemma_A_1
-- name    : TentNoise.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:44:52.445998+00:00
-- url     : https://prove2.me/theorems/030b4f92-d6ae-4184-8970-7bc579c477e6
-- title:
--   Lemma A.1 — reverse contraction: $W_1(K^*_\sigma(x,\cdot),K^*_\sigma(y,\cdot))\le\tfrac12|x-y|$
-- statement:
--   Let $\sigma\ge0$ and let $K^*_\sigma=H_\sigma F^*$ be the stationary reverse kernel of the noised tent map: $K^*_\sigma(y,\cdot)$ is the law of $a_B(\mathfrak r(y+\sigma Z))$ with $Z\sim\mathcal N(0,1)$, $B\sim\mathrm{Bern}(1/2)$ independent, $a_0(z)=z/2$, $a_1(z)=1-z/2$. Then for all $x,y\in[0,1]$,
--
--   $$
--   W_1\bigl(K^*_\sigma(x,\cdot),K^*_\sigma(y,\cdot)\bigr)\le\tfrac12|x-y|,
--   $$
--
--   where $W_1$ is the Wasserstein distance on $[0,1]$ with cost $|a-b|$.
--
--   This one-step backward contraction is the structural property behind every horizon-uniform estimate of the upper bound.
--
--   Differences from the source:
--   - encoding: W_1 on [0,1], states x, y ∈ [0,1] → the published transport cost with cost |a − b| on ℝ, valued in [0,∞], between kernels on ℝ, for x, y ∈ [0,1]; reason: the kernels are concentrated on [0,1]; same instances
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Lemma A.1, p.16 (PDF p.16)

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TentNoise_revKernel
import Definitions.Def_ModelRiskOT_WorstProb_TransportBall

open MeasureTheory ProbabilityTheory InformationTheory TeschlODE.Shared Set
open scoped ENNReal NNReal

namespace TentNoise

/-- **Lemma A.1 (Reverse contraction)** (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Lemma A.1, p.16):
`W₁(K*_σ(x, ·), K*_σ(y, ·)) ≤ ½|x − y|`.

**Formalization Note** `W₁` on `[0, 1]` is the published optimal transport cost with cost `|a − b|`;
`K*_σ = revKernel σ` is the law of `a_B(𝔯(y + σZ))`. Stated for `σ ≥ 0` (the paper's noise levels) and
`x, y ∈ [0, 1]` (the state space). -/
theorem lemma_A_1 (σ : ℝ) (hσ : 0 ≤ σ) (x y : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    ModelRiskOT.WorstProb.transportCost (fun a b : ℝ => |a - b|) (revKernel σ x) (revKernel σ y) ≤
      ENNReal.ofReal (1 / 2 * |x - y|) := by sorry

end TentNoise
