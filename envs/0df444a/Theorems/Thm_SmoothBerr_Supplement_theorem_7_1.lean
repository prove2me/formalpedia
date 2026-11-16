-- Prove2me | Theorems.Thm_SmoothBerr_Supplement_theorem_7_1
-- name    : SmoothBerr.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:00:33.50585+00:00
-- url     : https://prove2.me/theorems/c60a8eb0-bf92-4b68-bd76-ad364ee004fa
-- title:
--   Theorem 7.1 — hardness of weighted approximation, continuous version: degree $\gtrsim\log(\kappa)/\varepsilon$
-- statement:
--   There are universal constants such that the following holds whenever $\kappa\gtrsim1$ and $\kappa^{-0.1}\lesssim\varepsilon\lesssim1$. Let
--   $$
--   \mu:=\delta_{\kappa^{-1}}+(1-2\varepsilon)\,\mathrm{Unif}[2\varepsilon,1]. \tag{21}
--   $$
--   Every odd polynomial $p$ with
--   $$
--   \|xp-1\|^2_{L^2(\mu)}\ \le\ \varepsilon^2\|p\|^2_{L^2(\mu)} \tag{22}
--   $$
--   has degree $t\gtrsim\log(\kappa)/\varepsilon$.
--
--   This is the continuous form of Theorem 4.6, which follows from it by Gaussian quadrature: an odd polynomial cannot be large at $1/\kappa$ (where $\mu$ puts half its mass) while staying small on $[2\varepsilon,1]$ unless its degree grows like $\log(\kappa)/\varepsilon$.
--
--   **Formalization Note** All constants ($\kappa\ge K_0$, $\kappa^{-0.1}\le a\varepsilon$, $\varepsilon\le b'$, and the constant $c$ of the conclusion) are chosen first. $(1-2\varepsilon)\mathrm{Unif}[2\varepsilon,1]$ is Lebesgue measure on $[2\varepsilon,1]$; the squared norms are lower Lebesgue integrals. A polynomial is odd if $p(-x)=-p(x)$ for all $x$.
--
--   Differences from the source:
--   - encoding: κ ≳ 1, κ^{−0.1} ≲ ε ≲ 1; degree t ≳ log(κ)/ε → ∃ K₀ a b' c (a, b', c > 0) first; κ ≥ K₀, κ^{−0.1} ≤ a·ε, ε ≤ b'; c·(log κ/ε) ≤ natDegree p; reason: §3, p.4: ≲ hides a universal constant
--   - encoding: µ = δ_{κ⁻¹} + (1 − 2ε)Unif[2ε, 1]; ‖·‖²_{L2(µ)} → muHard κ ε = dirac (1/κ) + Lebesgue restricted to [2ε, 1]; lower Lebesgue integrals of squares; reason: (1 − 2ε)Unif[2ε, 1] is Lebesgue measure on [2ε, 1]
--   - encoding: odd polynomial p → p : ℝ[X] with p.eval (−x) = −p.eval x for all x; reason: the same polynomials
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Theorem 7.1, p.19, Eqs. (21), (22)

import Mathlib
import Definitions.Def_SmoothBerr_Supplement_muHard

open MeasureTheory Polynomial

namespace SmoothBerr.Supplement

/-- **Theorem 7.1 (Hardness of weighted approximation, continuous version)** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…, Theorem 7.1, p.19).

Fix `κ ≳ 1` and `κ^{−0.1} ≲ ε ≲ 1`, and let `µ := δ_{κ⁻¹} + (1 − 2ε) Unif[2ε, 1]` (21). Any odd
polynomial `p` with `‖xp − 1‖²_{L2(µ)} ≤ ε² ‖p‖²_{L2(µ)}` (22) has degree `≳ log(κ)/ε`.

**Formalization Note**
1. Every `≲`/`≳` is a universal constant chosen first (`K₀, a, b', c`), before `κ` and `ε`:
   `κ ≥ K₀`, `κ^{−0.1} ≤ a ε`, `ε ≤ b'`; the conclusion is `c · log κ/ε ≤ deg p`.
2. `µ` is `muHard κ ε`, the unit point mass at `1/κ` plus Lebesgue measure on `[2ε, 1]` (not
   normalized). The squared norms are lower Lebesgue integrals in `[0, ∞]`.
3. "Odd" is `p(−x) = −p(x)` for all `x`; the degree is `natDegree`. -/
theorem theorem_7_1 :
    ∃ K₀ a b' c : ℝ, 0 < a ∧ 0 < b' ∧ 0 < c ∧
      ∀ κ ε : ℝ, K₀ ≤ κ → κ ^ (-(1 / 10 : ℝ)) ≤ a * ε → ε ≤ b' →
        ∀ p : ℝ[X], (∀ x : ℝ, p.eval (-x) = -p.eval x) →
          ∫⁻ x, ENNReal.ofReal ((x * p.eval x - 1) ^ 2) ∂(muHard κ ε) ≤
            ENNReal.ofReal (ε ^ 2) * ∫⁻ x, ENNReal.ofReal (p.eval x ^ 2) ∂(muHard κ ε) →
          c * (Real.log κ / ε) ≤ p.natDegree := by sorry

end SmoothBerr.Supplement
