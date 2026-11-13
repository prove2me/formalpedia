-- Prove2me | Theorems.Thm_SaglamGV_walkProb_eq
-- name    : SaglamGV.walkProb_eq
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:50:32.417043+00:00
-- url     : https://prove2.me/theorems/7ecb7b61-c0b2-41a9-9825-b542611c0a52
-- title:
--   Walk identity: $e^\tau\Pr[W_\tau=e_{n+1}]=\sum_{\ell\ge3\text{ odd}}\frac{\tau^\ell}{\ell!}p_\ell$, $=e^{-\tau}\mathbb E_y\sinh(\tau\hat\mu)$, $=e^{-\tau}\mathbb E_y s(\tau\hat\mu)$
-- statement:
--   Let $\tau\ge0$ and let $W_\tau$ be the Poisson random walk on $\mathbb F_2^{n+1}$ with steps $(X_i,1)$, $X_i$ i.i.d. with law $\mu$. Then
--
--   1. $\displaystyle e^\tau\Pr[W_\tau=e_{n+1}]=\sum_{\substack{\ell\ge3\\ \ell\text{ odd}}}\frac{\tau^\ell}{\ell!}\,p_\ell$;
--   2. $\Pr[W_\tau=e_{n+1}]=e^{-\tau}\,\mathbb E_y\sinh(\tau\hat\mu(y))$;
--   3. $\Pr[W_\tau=e_{n+1}]=e^{-\tau}\,\mathbb E_y\,s(\tau\hat\mu(y))$, where $s(z)=\sinh z-z$.
--
--   The first identity conditions on the number of steps (the one-step term vanishes because $0\notin B_d$); the others combine it with Fourier inversion.
--
--   Differences from the source:
--   - generalization: τ = V2^{−m} for the chosen m, in the regime of §2 → every real τ ≥ 0 and every n, d; reason: the identities hold for every Poisson mean; they specialize to the paper's τ
--   - encoding: Pr[W_τ = e_{n+1}] for the continuous-time walk W_t = Σ_{i≤J_t}(X_i, 1) → walkProb, the Poisson(τ) mixture of the convolution powers of the step law; reason: this is the law of W_τ; only Pr[W_τ = e_{n+1}] is used, so no process is constructed
-- source:
--   M. Saglam, Linear codes exceeding the Gilbert–Varshamov bound, STOC 2027 submission manuscript (held version, sha256 ac6f2bba913aa15cfec8dda07a8e9e37b7186e145fef4719cb623dd04d15baa3), §2, p.3 (display e^τ Pr[W_τ = e_{n+1}] = Σ_{ℓ≥3, ℓ odd} τ^ℓ p_ℓ/ℓ!); §3.3, p.4 (displays with sinh and s)

import Mathlib
import Definitions.Def_SaglamGV_Code
import Definitions.Def_SaglamGV_Walk
import Definitions.Def_SaglamGV_Fourier
import Definitions.Def_SaglamGV_Analytic

namespace SaglamGV

/-- The walk identity (M. Saglam, *Linear codes exceeding the Gilbert–Varshamov bound*, STOC 2027 submission manuscript (held version, sha256 ac6f2bba…), §2, p.3: "Conditioning on the number of steps gives
e^τ Pr[W_τ = e_{n+1}] = Σ_{ℓ≥3, ℓ odd} (τ^ℓ/ℓ!) p_ℓ, where the one-step term vanishes because 0 ∉ B_d";
§3.3, p.4: "Pr[W_τ = e_{n+1}] = e^{−τ} E_y sinh(τµ̂(y))" and "We therefore have
Pr[W_τ = e_{n+1}] = e^{−τ} E_y s(τµ̂(y))").

For every $τ ≥ 0$, with $W_τ$ the compound-Poisson walk on $𝔽_2^{n+1}$ with steps $(X_i, 1)$,
$X_i ∼ μ$, all three identities hold, where $s(z) = \sinh z − z$.

**Formalization Note** $\Pr[W_τ = y]$ is `walkProb`, the Poisson($τ$) mixture of the convolution
powers of the step law (the law of the walk, not the series on the right). Stated for every $n, d$. -/
theorem walkProb_eq (n d : ℕ) (τ : ℝ) (hτ : 0 ≤ τ) :
    Real.exp τ * walkProb n d τ (eLast n) =
        ∑' ℓ : ℕ, (if 3 ≤ ℓ ∧ Odd ℓ then τ ^ ℓ / (ℓ.factorial : ℝ) * zeroSumProb n d ℓ else 0) ∧
      walkProb n d τ (eLast n) = Real.exp (-τ) * avgY (fun y => Real.sinh (τ * muHat n d y)) ∧
      walkProb n d τ (eLast n) = Real.exp (-τ) * avgY (fun y => sMinus (τ * muHat n d y)) := by sorry

end SaglamGV
