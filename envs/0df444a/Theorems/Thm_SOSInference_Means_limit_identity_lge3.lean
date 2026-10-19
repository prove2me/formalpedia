-- Prove2me | Theorems.Thm_SOSInference_Means_limit_identity_lge3
-- name    : SOSInference.Means.limit_identity_lge3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:25.043698+00:00
-- url     : https://prove2.me/theorems/c0d476c4-c6b3-45c6-9a13-f02f9c7f0b5f
-- title:
--   §7.2.6 — the $l\ge3$ limit identity: $\max_\zeta\{-2\zeta^{\mathsf T}z-\tfrac{2C}{l+2}\|\zeta\|_2^{l+2}\}=\tfrac{2l+2}{l+2}\|z\|_2^{1+1/(l+1)}/C^{1/(l+1)}$
-- statement:
--   Let $l\ge3$, $C>0$ and $z\in\mathbb R^l$. The function
--   $$\zeta\mapsto-2\zeta^{\mathsf T}z-\frac{2C}{l+2}\|\zeta\|_2^{l+2}$$
--   attains its maximum over $\mathbb R^l$, the maximum equals
--   $$\frac{2l+2}{l+2}\cdot\frac{\|z\|_2^{1+1/(l+1)}}{C^{1/(l+1)}},$$
--   and it is attained at $\zeta^*=-z\,\|z\|_2^{1/(l+1)-1}/C^{1/(l+1)}$ (which is $0$ when $z=0$).
--
--   With $C=c_0=\frac{\pi^{l/2}}{\Gamma(l/2+1)}\mathbb E[f_X(X_1)+\kappa f_Y(X_1)]$ and $z=\tilde Z\sim N(0,\mathrm{Var}(X))$, the maximum is the $l\ge3$ limit of Theorem 1.
--
--   **Formalization Note** The page prints $G(\zeta,n)=-\frac{2C}{l+2}\|\zeta\|_2^{l+2}+o(1)$; since $G$ is the expectation of a nonnegative variable, and the next display subtracts $\frac{2}{l+2}\|Z_n\|_2^{1+1/(l+1)}/C^{1/(l+1)}$, the sign is read as $+$. The scaling $n^{1/2+5/(4l+2)}$ printed in the last display of p. 48 is read as $n^{1/2+3/(2l+2)}$ (Theorem 1); it does not enter this deterministic identity.
-- source:
--   Blanchet, Kang, Sample Out-of-Sample Inference Based on Wasserstein Distance, arXiv:1605.01340v4, pp. 47–48, §7.2.6 (Step 6)

import Mathlib
import Definitions.Def_SOSInference_Means_sos

namespace SOSInference.Means

open scoped RealInnerProductSpace

/-- **The `l ≥ 3` limit identity**, §7.2.6, pp. 47–48 (Blanchet, Kang, Sample Out-of-Sample
Inference Based on Wasserstein Distance, arXiv:1605.01340v4, pp. 47–48). For `l ≥ 3`, `C > 0`
and `z ∈ ℝ^l`, the limit objective `ζ ↦ −2ζᵀz − (2C/(l+2)) ‖ζ‖₂^{l+2}` attains its maximum
`((2l+2)/(l+2)) ‖z‖₂^{1+1/(l+1)} / C^{1/(l+1)}` at
`ζ* = −z ‖z‖₂^{1/(l+1) − 1} / C^{1/(l+1)}`.

With `C = c₀ = π^{l/2}/Γ(l/2+1) E[f_X(X_1) + κ f_Y(X_1)]` the maximum is `φ_l(z)`, the `l ≥ 3`
limit of Theorem 1.

**Formalization Note.** The page prints `G(ζ, n) = −(2C/(l+2)) ‖ζ‖^{l+2} + o(1)`, but `G` is the
expectation of a nonnegative variable and the next display subtracts `(2/(l+2))‖Z_n‖^{…}/C^{…}`;
the sign is read as `+`, i.e. the objective is `−2ζᵀz − G∞(ζ)` with `G∞(ζ) = (2C/(l+2))‖ζ‖^{l+2}`.
The printed scaling `n^{1/2+5/(4l+2)}` of the last display is read as `n^{1/2+3/(2l+2)}`
(Theorem 1); it does not enter this deterministic identity. At `z = 0`, Lean's `0^r = 0` (`r ≠ 0`)
gives `ζ* = 0` and value `0`, which is correct. -/
theorem limit_identity_lge3 {l : ℕ} (hl : 3 ≤ l) (C : ℝ) (hC : 0 < C) (z : E l) :
    IsGreatest
      (Set.range fun ζ : E l => -2 * ⟪ζ, z⟫ - 2 * C / ((l : ℝ) + 2) * ‖ζ‖ ^ (l + 2))
      ((2 * (l : ℝ) + 2) / ((l : ℝ) + 2) * ‖z‖ ^ (1 + 1 / ((l : ℝ) + 1)) /
        C ^ (1 / ((l : ℝ) + 1))) ∧
    ∀ ζstar : E l, ζstar = -(‖z‖ ^ (1 / ((l : ℝ) + 1) - 1) / C ^ (1 / ((l : ℝ) + 1))) • z →
      -2 * ⟪ζstar, z⟫ - 2 * C / ((l : ℝ) + 2) * ‖ζstar‖ ^ (l + 2) =
        (2 * (l : ℝ) + 2) / ((l : ℝ) + 2) * ‖z‖ ^ (1 + 1 / ((l : ℝ) + 1)) /
          C ^ (1 / ((l : ℝ) + 1)) := by sorry

end SOSInference.Means
