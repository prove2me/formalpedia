-- Prove2me | Theorems.Thm_RandProdExp_TwoSided_theorem_5_1
-- name    : RandProdExp.TwoSided.theorem_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:19:24.994676+00:00
-- url     : https://prove2.me/theorems/c2e70bbf-16a1-4015-aca2-037a09dcf0d6
-- title:
--   Theorem 5.1 — random codes over a prime field $p=O_D(2^{n^D}n^D\log n)$ are two-sided $\gamma(\varepsilon,D)$-product expanding with probability $\ge1-1/\log(n+1)$
-- statement:
--   For every $D\ge1$ there is a constant $C_D>0$ such that the following holds. Let $0<\rho<1/2$, $0<\varepsilon\le\varepsilon_0(D,\rho)$, $n\ge N^*_{D,\varepsilon}$ and let $k_1,\dots,k_D$ be integers with $\rho n\le k_i\le(1-\rho)n$, where
--   $$C_\rho=3(1+\rho^{-1/2}),\quad A_{D,\rho}=2(4C_\rho)^D(1+4/\rho)^D,\quad \varepsilon_0(D,\rho)=\frac1{2^{D+2}A_{D,\rho}^2},\quad N^*_{D,\varepsilon}=\Big\lceil\max\Big\{16\Big(\frac{192D}e\Big)^{24},(2^D\varepsilon)^{-2}\Big\}\Big\rceil .$$
--   Then there is a prime $p\le C_D\,2^{n^D}n^D\log n$ such that independent uniformly random codes $C_i\in\mathrm{Gr}_p(n,k_i)$ are two-sided $\gamma(\varepsilon,D)$-product expanding with probability
--   $$\Pr\big[(C_i)\text{ and }(C_i^\perp)\text{ are both }\gamma(\varepsilon,D)\text{-product expanding}\big]\ \ge\ 1-\frac1{\log(n+1)},\qquad \gamma(\varepsilon,D)=\frac{\varepsilon^D}{D(2^D+1)^D}.$$
--   This is the paper's main result: two-sided product expansion, the property behind good quantum LDPC codes and locally testable codes, holds for random codes of every constant dimension $D$ over a prime field of explicit size.
--
--   Differences from the source:
--   - encoding: p = O_D(2^{n^D} n^D log n) → ∃ C_D > 0 (depending on D only, chosen before ρ, ε, n, k), p ≤ C_D · 2^{n^D} · n^D · Real.log n; reason: O_D is a constant depending only on D (Theorem 1, p. 4)
--   - encoding: independent uniformly random codes C_i ∈ Gr_p(n, k_i) → uniform counting probability on ∏_i Gr(n, k_i) over ZMod p (codeProb); reason: independent uniform choices on finite sets
--   - encoding: n ≥ N*_{D,ε}, log natural → (N*_{D,ε} : ℝ) ≤ n with N* the integer ceiling; Real.log; reason: same condition for integer n; the paper's log is natural (Theorem 3.25, p. 67)
-- source:
--   Chattopadhyay, Ringach, Spooner, Product Expansion of Random Codes via Analytic Techniques, STOC 2027 submission (manuscript sha256 9e4ac2d1…), p. 34, Theorem 5.1

import Mathlib
import Definitions.Def_RandProdExp_TwoSided_Codes
import Definitions.Def_RandProdExp_TwoSided_Params

namespace RandProdExp.TwoSided

/-- **Theorem 5.1** (p. 34). For every `D ≥ 1` there is a constant `C_D > 0` such that for all
`0 < ρ < 1/2`, `0 < ε ≤ ε₀(D, ρ)`, `n ≥ N*_{D,ε}` and integers `ρ n ≤ k_i ≤ (1 − ρ) n`, there is a prime
`p ≤ C_D 2^{n^D} n^D log n` such that independent uniformly random codes `C_i ∈ Gr_p(n, k_i)` are
two-sided `γ(ε, D)`-product expanding with probability at least `1 − 1/log(n + 1)`, where
`γ(ε, D) = ε^D / (D (2^D + 1)^D)`. -/
theorem theorem_5_1 (D : ℕ) (hD : 1 ≤ D) :
    ∃ CD : ℝ, 0 < CD ∧
      ∀ (ρ ε : ℝ), 0 < ρ → ρ < 1 / 2 → 0 < ε → ε ≤ eps0 D ρ →
      ∀ n : ℕ, (Nstar D ε : ℝ) ≤ n →
      ∀ k : Fin D → ℕ, (∀ i, ρ * n ≤ k i ∧ (k i : ℝ) ≤ (1 - ρ) * n) →
      ∃ (p : ℕ) (_ : Fact p.Prime),
        (p : ℝ) ≤ CD * 2 ^ (n ^ D) * (n : ℝ) ^ D * Real.log n ∧
        1 - 1 / Real.log (n + 1) ≤
          codeProb (ZMod p) n k (fun C =>
            IsTwoSidedProductExpanding (gammaConst ε D) (fun i => (C i).1)) := by sorry

end RandProdExp.TwoSided
