-- Prove2me | Theorems.Thm_WarrantyMatch_moment_identity
-- name    : WarrantyMatch.moment_identity
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:38:15.684989+00:00
-- url     : https://prove2.me/theorems/b6a021f3-5ecc-4c97-9ba9-49a6e9d6d9b8
-- title:
--   §EC.2 — $E[(1+(l+Z)\epsilon)^2]=(1+a_r\epsilon)^2+b_r\epsilon^2$, with $E[Z]=\frac{y+d}{d}$, $\mathrm{var}(Z)=\frac{y(y+d)}{d^2}$
-- statement:
--   Let $Z$ be a geometric number of trials with parameter $d/(y+d)$, where $d>0$ and $y\ge0$: $P(Z=k)=\frac{d}{y+d}\bigl(\frac{y}{y+d}\bigr)^{k-1}$ for $k=1,2,\dots$. Then $Z$ and $Z^2$ are integrable,
--   $$
--   E[Z]=\frac{y+d}{d},\qquad \operatorname{var}(Z)=\frac{y(y+d)}{d^2},
--   $$
--   and for every $l\in\mathbb N$ and every $\varepsilon\in\mathbb R$,
--   $$
--   E\bigl[(1+(l+Z)\varepsilon)^2\bigr]=\bigl(1+(l+E[Z])\varepsilon\bigr)^2+\operatorname{var}(Z)\,\varepsilon^2=(1+a_r\varepsilon)^2+b_r\varepsilon^2,
--   $$
--   with $a_r=l+\frac{y+d}{d}$ and $b_r=\frac{y(y+d)}{d^2}$.
--
--   These identities turn the bound of the conditioning step into the closed-form constant of Proposition 1.
--
--   **Formalization Note** $E[Z]$ is the Bochner integral and $\operatorname{var}(Z)$ is Mathlib's `variance` of $Z$ cast to $\mathbb R$; neither is defined by its closed form.
--
--   Differences from the source:
--   - reading: geometric random variable with parameter d/(y + d) → Z ∈ {1, 2, …} with P(Z = k + 1) = (1 − q)^k q; reason: the paper's E[Z] = (y + d)/d fixes the number-of-trials convention
--   - encoding: E[Z], var(Z) used without comment → integrability of Z and Z² stated as conclusions; reason: Lean's integral of a non-integrable function is 0, so integrability makes the moments the true ones
--   - generalization: d, y the constant demand and inventory counts, ε ≥ 0 → real d > 0, y ≥ 0 and any real ε; reason: the identities hold verbatim for these values; the paper's case is a special case
-- source:
--   Calmon–Graves–Lemmens, Warranty Matching in a Consumer Electronics Closed-Loop Supply Chain, INSEAD WP 2020/03/TOM (SSRN 3357683), §EC.2, proof of Proposition 1, displays after "Since E[(l + Z)^2] = var(Z) + (E[l + Z])^2", p.ec4, and "Recall that Z follows a geometric distribution with parameter d/(y + d)", p.ec5

import Mathlib
import Definitions.Def_WarrantyMatch_Model

open MeasureTheory ProbabilityTheory

namespace WarrantyMatch

/-- **§EC.2, moments of `Z`.** Let `Z` be a geometric number of trials with parameter
`d/(y + d)` (`d > 0`, `y ≥ 0`). Then `Z` and `Z²` are integrable, `E[Z] = (y + d)/d`,
`var(Z) = y(y + d)/d²`, and for every lead time `l` and every `ε`,
`E[(1 + (l + Z)ε)²] = (1 + (l + E[Z])ε)² + var(Z)ε² = (1 + a_r ε)² + b_r ε²`.
Calmon–Graves–Lemmens, *Warranty Matching in a Consumer Electronics Closed-Loop Supply Chain*,
INSEAD WP 2020/03/TOM (SSRN 3357683), §EC.2, proof of Proposition 1, displays after "Since E[(l + Z)²] = var(Z) + (E[l + Z])²",
p.ec4, and "Recall that Z follows a geometric distribution …", p.ec5.

**Formalization Note** `E[Z]` is the Bochner integral and `var(Z)` is Mathlib's `variance` of
`Z` cast to `ℝ`; neither is defined by its closed form. -/
theorem moment_identity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℕ) (d y ε : ℝ) (l : ℕ) (hd : 0 < d) (hy : 0 ≤ y)
    (hZ : IsGeomTrials P Z (d / (y + d))) :
    Integrable (fun ω => (Z ω : ℝ)) P ∧ Integrable (fun ω => (Z ω : ℝ) ^ 2) P ∧
    ∫ ω, (Z ω : ℝ) ∂P = (y + d) / d ∧
    variance (fun ω => (Z ω : ℝ)) P = y * (y + d) / d ^ 2 ∧
    ∫ ω, (1 + ((l : ℝ) + Z ω) * ε) ^ 2 ∂P =
      (1 + ((l : ℝ) + ∫ ω, (Z ω : ℝ) ∂P) * ε) ^ 2 + variance (fun ω => (Z ω : ℝ)) P * ε ^ 2 ∧
    ∫ ω, (1 + ((l : ℝ) + Z ω) * ε) ^ 2 ∂P = (1 + aR l y d * ε) ^ 2 + bR y d * ε ^ 2 := by sorry

end WarrantyMatch
