-- Prove2me | Theorems.Thm_SOSInference_Means_limit_identity_l2
-- name    : SOSInference.Means.limit_identity_l2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:03.266989+00:00
-- url     : https://prove2.me/theorems/adc04e36-429f-4a9a-b6ba-49971a8a63ef
-- title:
--   §7.2.5 — the $l=2$ limit identity: $\max_\zeta\{-2\zeta^{\mathsf T}z-\|\zeta\|_2^2\tilde\eta(\zeta)\}=\rho(2-\tilde\eta(\rho z)\rho)\|z\|_2^2$
-- statement:
--   Assume A1)–A4) with $l=2$, and let $\tau(0)$, $\tilde\eta$ and $\rho$ be as in Theorem 1.
--
--   1. For every $\zeta\in\mathbb R^2$, $\ \|\zeta\|_2^2\,\tilde\eta(\zeta)=\mathbb E\big[\max(\|\zeta\|_2^2-\tau(0),0)\big]$; this is the limit $\lim_n G(\zeta,n)$ computed on p. 45.
--   2. For $z\ne0$, the limiting objective $\zeta\mapsto-2\zeta^{\mathsf T}z-\|\zeta\|_2^2\,\tilde\eta(\zeta)$ attains its maximum, and
--   $$\max_{\zeta\in\mathbb R^2}\Big\{-2\zeta^{\mathsf T}z-\|\zeta\|_2^2\,\tilde\eta(\zeta)\Big\}=\rho(z)\big(2-\tilde\eta(\rho(z)z)\,\rho(z)\big)\|z\|_2^2 .$$
--   3. The maximum is attained at $\zeta^*=-\rho(z)\,z$.
--
--   Evaluated at $z=\tilde Z\sim N(0,\mathrm{Var}(X))$, the right-hand side is the $l=2$ limit of Theorem 1.
--
--   **Formalization Note** The page prints the plugged-in value as $2\rho\|\tilde Z\|_2^2-\rho^2\tilde\eta(\tilde Z)\|\tilde Z\|_2^2$. With $\zeta_n^*=-\rho Z_n$, the term $G(\zeta_n^*,n)=\|\zeta_n^*\|_2^2\tilde\eta(\zeta_n^*)+o(1)$ equals $\rho^2\|Z_n\|_2^2\,\tilde\eta(\rho Z_n)+o(1)$, so the value is stated with $\tilde\eta(\rho(z)z)$.
-- source:
--   Blanchet, Kang, Sample Out-of-Sample Inference Based on Wasserstein Distance, arXiv:1605.01340v4, p. 45, §7.2.5 (Step 5)

import Mathlib
import Definitions.Def_SOSInference_Means_tauLaw

namespace SOSInference.Means

open MeasureTheory
open scoped RealInnerProductSpace

/-- **The `l = 2` limit identity**, §7.2.5, p. 45 (Blanchet, Kang, Sample Out-of-Sample Inference
Based on Wasserstein Distance, arXiv:1605.01340v4, p. 45). Under A1)–A4) with `l = 2`:
1. for every `ζ`, `‖ζ‖₂² η̃(ζ) = E[max(‖ζ‖₂² − τ(0), 0)]` (the limit `G∞(ζ)` of `G(ζ, n)`);
2. for `z ≠ 0`, the limit objective `ζ ↦ −2ζᵀz − ‖ζ‖₂² η̃(ζ)` attains its maximum
   `ρ(z)(2 − η̃(ρ(z) z) ρ(z)) ‖z‖₂² = φ₂(z)`;
3. the maximum is attained at `ζ* = −ρ(z) z`.

**Formalization Note.** The page prints the plugged-in value as `2ρ‖Z̃‖² − ρ²η̃(Z̃)‖Z̃‖²`; with
`ζ*_n = −ρ Z_n` the term `G(ζ*_n, n) = ‖ζ*_n‖²η̃(ζ*_n) + o(1)` is `ρ²‖Z_n‖²η̃(ρ Z_n)`, so the value
is stated with `η̃(ρ(z) z)` (`φ₂`). -/
theorem limit_identity_l2 (M : Model 2) (hM : M.Standing) (z : E 2) (hz : z ≠ 0) :
    (∀ ζ : E 2, ‖ζ‖ ^ 2 * etatilde M ζ = ∫ t, max (‖ζ‖ ^ 2 - t) 0 ∂(tauLaw M 0)) ∧
    IsGreatest (Set.range fun ζ : E 2 => -2 * ⟪ζ, z⟫ - ‖ζ‖ ^ 2 * etatilde M ζ) (phi2 M z) ∧
    -2 * ⟪-(rho M z) • z, z⟫ - ‖-(rho M z) • z‖ ^ 2 * etatilde M (-(rho M z) • z) =
      phi2 M z := by sorry

end SOSInference.Means
