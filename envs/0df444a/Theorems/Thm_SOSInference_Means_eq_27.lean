-- Prove2me | Theorems.Thm_SOSInference_Means_eq_27
-- name    : SOSInference.Means.eq_27
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:20.22121+00:00
-- url     : https://prove2.me/theorems/c923b297-759f-4a30-b9a7-3f54e5e92a88
-- title:
--   (27) — the simplified SOS profile function in terms of nearest-point distances
-- statement:
--   Let $x_1,\dots,x_n\in\mathbb R^l$ ($n\ge1$), and let $(z_j)_{j\in J}$ be a finite family of points of $\mathbb R^l$ that contains every $x_i$ and, for every $i$, at least one point different from $x_i$. Take $\theta_*=0$ and assume that the linear program (21) is feasible. For $\lambda\in\mathbb R^l$ let
--   $$D_i(\lambda)=\min_{j:\ z_j\ne x_i}\|z_j-(x_i+\lambda)\|_2^2$$
--   be the squared distance from $x_i+\lambda$ to the nearest point of the family different from $x_i$. Then
--   $$R_n^W(0)=\max_{\lambda\in\mathbb R^l}\Big\{-2\lambda^{\mathsf T}\bar X_n-\frac1n\sum_{i=1}^n\max\big(\|\lambda\|_2^2-D_i(\lambda),\,0\big)\Big\},$$
--   and the maximum is attained.
--
--   In the paper $D_i(\lambda)$ is written $T_i^{2/l}(n,\lambda)/n^{2/l}$, the rescaled first-arrival time of a counting process; this representation is what links the SOS function to Poisson approximations and drives the dimension-dependent rates of Theorem 1.
--
--   **Formalization Note** (27) is obtained by the substitution $\lambda\leftarrow2\lambda$; after it, the nearest-point distance is measured from $x_i+\lambda$ (the centre $X_i+\lambda/2$ before the substitution), while the page keeps the symbol $T_i(n,\lambda)$. The distance is written out with the centre $x_i+\lambda$. The condition $z_j\ne x_i$ is on values; the excluded points contribute exactly $\|\lambda\|_2^2$, which is the $\min(\cdot,\|\lambda\|_2^2/4)$ term of Step 3.
-- source:
--   Blanchet, Kang, Sample Out-of-Sample Inference Based on Wasserstein Distance, arXiv:1605.01340v4, p. 41, §7.2.3, (27)

import Mathlib
import Definitions.Def_SOSInference_Means_sos

namespace SOSInference.Means

open scoped RealInnerProductSpace

/-- **(27)**, §7.2.3, p. 41 (Blanchet, Kang, Sample Out-of-Sample Inference Based on Wasserstein
Distance, arXiv:1605.01340v4, p. 41, (27)): the simplified SOS profile function.

Let `x_1, …, x_n` (`n ≥ 1`) be points of `ℝ^l` and `z` a finite family containing every `x_i`
and, for every `i`, at least one point different from `x_i`. Take `θ* = 0` and assume the LP (21)
is feasible. For `λ ∈ ℝ^l` let `D_i(λ)` be the squared distance from `x_i + λ` to the nearest
`z_j ≠ x_i`. Then
`R_n^W(0) = max_λ {−2λᵀX̄_n − (1/n) Σ_i max(‖λ‖₂² − D_i(λ), 0)}`,
the maximum being attained.

**Formalization Note.** In (27), after the substitution `λ ← 2λ`, the printed term
`T_i^{2/l}(n, λ)/n^{2/l}` is the squared distance from `X_i + λ/2` *before* the substitution,
i.e. from `x_i + λ` after it; `D_i(λ)` is written out with the centre `x_i + λ`. The condition
"`z_j ≠ x_i`" is on values (as in `N_n^{(i)}`, p. 38); the excluded terms contribute `‖λ‖₂²` and
are the `min(·, ‖λ‖₂²/4)` of Step 3. -/
theorem eq_27 {l n : ℕ} {ι : Type*} [Fintype ι] (hn : 0 < n) (x : Fin n → E l) (z : ι → E l)
    (hx : ∀ i, ∃ j, z j = x i) (hother : ∀ i, ∃ j, z j ≠ x i)
    (hfeas : ∃ cpl, IsFeasibleCoupling (n := n) z 0 cpl) :
    IsGreatest
      (Set.range fun lam : E l =>
        -2 * ⟪lam, xbar x⟫ - (1 / (n : ℝ)) * ∑ i,
          max (‖lam‖ ^ 2 - ⨅ j : {j : ι // z j ≠ x i}, ‖z j - (x i + lam)‖ ^ 2) 0)
      (sos x z 0) := by sorry

end SOSInference.Means
