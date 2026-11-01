-- Prove2me | Theorems.Thm_PSDPolyApprox_noise_qy
-- name    : PSDPolyApprox.noise_qy
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:52:55.900607+00:00
-- url     : https://prove2.me/theorems/fb6460d2-a21a-4bb1-9e42-c3b07668713b
-- title:
--   §3, p.5 — $T_\rho q_y=1+\rho^2(q_y-1)$ for $q_y(x)=\frac1n(x^{\mathsf T}y)^2$
-- statement:
--   Let $n\ge1$ and fix $y\in H_n$. For the function $q_y(x)=\frac1n(x^{\mathsf T}y)^2$ on $H_n$ and every real $\rho$,
--   $$
--   T_\rho q_y(x)=1+\rho^2\bigl(q_y(x)-1\bigr)\qquad\text{for all }x\in H_n .
--   $$
--   Applied to the factorization identity (5), it turns the diagonal entries $q_y(y)=n$ into the lower bound (7) that drives the counting argument.
--
--   Differences from the source:
--   - generalization: ρ ∈ [0, 1] (the range on which T_ρ is introduced) → every real ρ; reason: T_ρ is the Fourier formula for every real ρ; the identity holds for all ρ and specializes to the paper's range
--   - encoding: n implicit → n ≥ 1; reason: at n = 0 the factor 1/n is undefined (Lean's 1/0 = 0)
--   - encoding: H_n = {−1, 1}^n and the uniform measure µ → functions Fin n → ℤˣ; µ(S) = |S|/2^n and E[f] = 2^{−n} Σ f; reason: ℤˣ = {±1}; same instances
-- source:
--   Fawzi, On polyhedral approximations of the positive semidefinite cone, arXiv:1811.09649v1, §3, p.5

import Mathlib
import Definitions.Def_PSDPolyApprox_noise
import Definitions.Def_PSDPolyApprox_qy

namespace PSDPolyApprox

/-- **The noise operator on `q_y`.**
Fawzi, arXiv:1811.09649v1, §3, p.5: "For each ﬁxed y, let qy(x) = 1/n(xT y)2. … It is easy to
verify that for ﬁxed y, Tρqy(x) = 1+ρ2(qy(x)−1)."

For `n ≥ 1`, every `y ∈ Hₙ` and every real `ρ`: `T_ρ q_y = 1 + ρ²(q_y − 1)` pointwise on `Hₙ`.

**Formalization Note.** `T_ρ` is defined by its Fourier formula for every real `ρ`; the paper
uses `ρ ∈ [0, 1]`. `n ≥ 1` excludes `n = 0`, where `(1/0) = 0` in Lean. -/
theorem noise_qy (n : ℕ) (hn : 1 ≤ n) (y : Cube n) (ρ : ℝ) :
    noise ρ (qy n y) = fun x => 1 + ρ ^ 2 * (qy n y x - 1) := by sorry

end PSDPolyApprox
