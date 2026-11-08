-- Prove2me | Theorems.Thm_PureDPQR_proposition_23
-- name    : PureDPQR.proposition_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T08:00:51.823885+00:00
-- url     : https://prove2.me/theorems/fb4e156b-6089-485a-af89-30e80c3b210c
-- title:
--   Proposition 23, p.26 — Algorithm 2 has $\mathrm{err}_Q\le C_0\min\{1,\sqrt{\log(2d/\beta)\log(2k)/(N\varepsilon)}\}$ w.p. $\ge1-9\beta/32$
-- statement:
--   **Proposition 23** (High-probability accuracy). There is a universal constant $C_0$ such that the following holds. Let $N\ge1$, $d\ge2$, $k\ge1$, $0<\varepsilon\le1$, $0<\beta<\frac12$ and $Q\subset[0,1]^d$ a table of $k$ queries. For every $h\in H_{N,d}$, the output $\hat p=D(y)$ of Algorithm 2 satisfies, with probability at least $1-9\beta/32$,
--
--   $$\mathrm{err}_Q(\hat p,h)\le C_0\min\Big\{1,\sqrt{\frac{\log(2d/\beta)\log(2k)}{N\varepsilon}}\Big\}.$$
--
--   This is the accuracy half of Theorem 2.
--
--   **Formalization Note** $C_0$ is chosen before all parameters; the probability is taken under `alg2Law`.
--
--   Differences from the source:
--   - encoding: "with probability at least 1 − 9β/32" → ofReal(1 − 9β/32) ≤ alg2Law h {p | errQ(p, h) ≤ …}; reason: the law of p̂ is alg2Law; same event
--   - encoding: Algorithm 2, a randomized procedure → its output law alg2Law = Σ_y Q_h(y) δ_{D(y)}, with Q_h(y) the integral smoothed; reason: Z_j = B_j L_j has law (1−π)δ₀ + πLap(κ) and y given Z has law p_{h+Z}, so this is the law of the output
--   - encoding: Lap(κ) of rate κ → PrivLearn.Generic.laplace κ⁻¹ (scale parameter); reason: the published Laplace law is parametrized by its scale; same law
--   - encoding: 1-based labels, coordinates and rounds → Fin (2k), Fin d, Fin T; reason: Lean convention
-- source:
--   Zou, Pure Differentially Private Query Release via Laplace Input Smoothing, arXiv:2611.04721 (held version, sha256 69b70d59…), Proposition 23, p.26 (PDF p.27); §6 preamble, p.25

import Mathlib
import Definitions.Def_PureDPQR_IsDP
import Definitions.Def_PureDPQR_errQ
import Definitions.Def_PureDPQR_alg2Law

namespace PureDPQR

/-- **Proposition 23** (High-probability accuracy), p.26 (PDF p.27).

Z. Zou, *Pure Differentially Private Query Release via Laplace Input Smoothing*, arXiv:2611.04721
(held version, sha256 69b70d59…).

"There is a universal constant C_0 such that, for every h ∈ H_{N,d}, the output p̂ = D(y) of
Algorithm 2 satisfies, with probability at least 1 − 9β/32,
errQ(p̂, h) ≤ C_0 min{1, √(log(2d/β) log(2k)/(Nε))}."

Parameter ranges (§6, p.25): those of Theorem 2.

**Formalization Note.** The universal constant `C₀` is chosen before all parameters. The law of
`p̂` is `alg2Law`; "with probability at least `1 − 9β/32`" is
`ofReal (1 − 9β/32) ≤ alg2Law h {p | errQ(p, h) ≤ …}`. Under the ranges every logarithm and
the square root have positive arguments. -/
theorem proposition_23 :
    ∃ C₀ : ℝ, ∀ (N d k : ℕ) (ε β : ℝ), 1 ≤ N → 2 ≤ d → 1 ≤ k → 0 < ε → ε ≤ 1 → 0 < β →
      β < 1 / 2 → ∀ Q : Fin k → Fin d → ℝ, (∀ i j, Q i j ∈ Set.Icc (0 : ℝ) 1) →
        ∀ h ∈ histograms N d,
          ENNReal.ofReal (1 - 9 * β / 32) ≤
            alg2Law N d k ε β Q h {p | errQ N Q p h ≤
              C₀ * min 1 (Real.sqrt (Real.log (2 * d / β) * Real.log (2 * k) /
                ((N : ℝ) * ε)))} := by sorry

end PureDPQR
