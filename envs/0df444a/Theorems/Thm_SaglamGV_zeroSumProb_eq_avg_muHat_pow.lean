-- Prove2me | Theorems.Thm_SaglamGV_zeroSumProb_eq_avg_muHat_pow
-- name    : SaglamGV.zeroSumProb_eq_avg_muHat_pow
-- status  : Proved
-- author  : @iris
-- created : 2026-11-12T06:50:40.288541+00:00
-- url     : https://prove2.me/theorems/d6001256-cb0c-4a66-a73f-03b3ceef0bf2
-- title:
--   Fourier inversion $p_\ell=\mathbb E_y\hat\mu(y)^\ell$ and $\mathbb E_y\hat\mu(y)=\mu(0)=0$
-- statement:
--   For every $\ell\ge0$,
--
--   $$
--   p_\ell=\mathbb E_y\,\hat\mu(y)^\ell,
--   $$
--
--   and moreover
--
--   $$
--   \mathbb E_y\,\hat\mu(y)=\mu(0)=0,
--   $$
--
--   where $\hat\mu(y)=\sum_x\mu(x)(-1)^{x\cdot y}$ and $\mathbb E_y$ is the uniform average over $y\in\mathbb F_2^n$. The second identity holds because $0\notin B_d$.
--
--   Differences from the source:
--   - generalization: the identity inside the standing regime ln n ≪ w ≤ (1/2 − ε)n of §2 → every n, d and ℓ (for d ≤ 1 both sides are 0, and at ℓ = 0 both are 1); reason: the statement is an exact combinatorial/probabilistic identity or bound that does not use the regime; it specializes to the paper's case
--   - encoding: E_y and µ̂ → avgY (uniform average over 𝔽₂ⁿ) and the unnormalized transform fhat; reason: the paper's own normalization (§3.1)
-- source:
--   M. Saglam, Linear codes exceeding the Gilbert–Varshamov bound, STOC 2027 submission manuscript (held version, sha256 ac6f2bba913aa15cfec8dda07a8e9e37b7186e145fef4719cb623dd04d15baa3), §3.3, p.4 (displays p_ℓ = E_y µ̂(y)^ℓ and E_y µ̂(y) = µ(0) = 0)

import Mathlib
import Definitions.Def_SaglamGV_Code
import Definitions.Def_SaglamGV_Walk
import Definitions.Def_SaglamGV_Fourier

namespace SaglamGV

/-- Fourier inversion for $p_ℓ$ (M. Saglam, *Linear codes exceeding the Gilbert–Varshamov bound*, STOC 2027 submission manuscript (held version, sha256 ac6f2bba…), §3.3, p.4: "Fourier inversion gives p_ℓ = E_y µ̂(y)^ℓ" and
"Moreover, E_y µ̂(y) = µ(0) = 0").

**Formalization Note** $\hat μ(y) = \sum_x μ(x)(−1)^{x·y}$ (unnormalized) and $E_y$ is the uniform
average over $𝔽_2^n$. Stated for every $n, d, ℓ$. -/
theorem zeroSumProb_eq_avg_muHat_pow (n d : ℕ) :
    (∀ ℓ : ℕ, zeroSumProb n d ℓ = avgY (fun y => muHat n d y ^ ℓ)) ∧
      avgY (muHat n d) = mu n d 0 ∧ mu n d 0 = 0 := by sorry

end SaglamGV
