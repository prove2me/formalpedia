-- Prove2me | Theorems.Thm_PermLimits_Cauchy_weak_conv_iff_uniform_cdf
-- name    : PermLimits.Cauchy.weak_conv_iff_uniform_cdf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T21:24:05.533983+00:00
-- url     : https://prove2.me/theorems/fb8bd1d8-beb6-4396-b357-78dfb808aaf9
-- title:
--   Lemma 2.1: with uniform marginals, weak convergence equals uniform convergence of joint cdfs
-- statement:
--   Let $(\mu_n)_{n\ge1}$ and $\mu$ be probability measures on $[0,1]^2$, with random points $(X_n,Y_n)$, $(X,Y)$ and joint distribution functions $F_n$, $F$. Assume $X_n,Y_n\sim U[0,1]$ for every $n$. Then
--   $$(X_n,Y_n)\xrightarrow{d}(X,Y)\iff \|F_n-F\|_\infty=\sup_{x,y\in[0,1]}|F_n(x,y)-F(x,y)|\to0 .$$
--
--   For general measures on the square only the implication from right to left holds; the uniform marginals are what make the joint cdfs uniformly equicontinuous. The lemma translates weak convergence into a metric statement, which is how rectangular distance enters the theory.
--
--   **Formalization Note** Weak convergence is tested against all continuous functions on the compact square. Uniform convergence of $F_n$ to $F$ is `TendstoUniformly` on $[0,1]^2$. No marginal assumption is made on $\mu$, as in the source.
-- source:
--   Hoppen, Kohayakawa, Moreira, Ráth, Sampaio, Limits of permutation sequences, arXiv:1103.5844v2, https://arxiv.org/abs/1103.5844v2, p. 7, Lemma 2.1

import Mathlib
import Definitions.Def_PermLimits_Shared_LimitMeasure
import Definitions.Def_PermLimits_Shared_LimitConvergence
open PermLimits.Shared

namespace PermLimits.Cauchy

open MeasureTheory Filter unitInterval

/-- **Lemma 2.1** (Hoppen et al., *Limits of permutation sequences*, arXiv:1103.5844v2, p. 7).
Let `(μ_n)` and `μ` be probability measures on `[0,1]²`, with joint distribution functions
`F_n` and `F`, and assume that for every `n` both marginals of `μ_n` are uniform on `[0, 1]`.
Then `μ_n ⇒ μ` (convergence in distribution `(X_n, Y_n) →ᵈ (X, Y)`) if and only if
`‖F_n − F‖_∞ = sup_{x,y ∈ [0,1]} |F_n(x, y) − F(x, y)| → 0`.

**Formalization Note.** Weak convergence is the paper's (9) with continuous test functions on the
compact square (`WeakConvMeasures`). `‖F_n − F‖_∞ → 0` is `TendstoUniformly` of the joint
distribution functions on `[0,1]²`. No marginal assumption is made on `μ`, as in the paper. -/
theorem weak_conv_iff_uniform_cdf (μs : ℕ → Measure (I × I)) (μ : Measure (I × I))
    (hμs : ∀ n, IsProbabilityMeasure (μs n)) [IsProbabilityMeasure μ]
    (hX : ∀ n, (μs n).map Prod.fst = volume) (hY : ∀ n, (μs n).map Prod.snd = volume) :
    WeakConvMeasures μs μ ↔
      TendstoUniformly (fun n (p : I × I) => jointCDF (μs n) p.1 p.2)
        (fun p : I × I => jointCDF μ p.1 p.2) atTop := by sorry

end PermLimits.Cauchy
