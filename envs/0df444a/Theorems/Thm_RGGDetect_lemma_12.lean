-- Prove2me | Theorems.Thm_RGGDetect_lemma_12
-- name    : RGGDetect.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:40:49.031009+00:00
-- url     : https://prove2.me/theorems/9a66ae27-62d1-4af8-b9f2-66112576649d
-- title:
--   Lemma 12 — bounds on $b_h/N_h$ for products of zonal polynomials
-- statement:
--   There is an absolute constant $C$ such that for every $d\ge3$, $h\ge0$, $k\ge1$ and $\mathbf a\in\mathbb N^k$,
--
--   $$
--   0\le\frac{b_h}{N_h}\le\min\left\{\frac1{N_{\max\{h,a_1,\dots,a_k\}}},\Big(\frac{C(h+A)}d\Big)^{(h+A)/2}\right\}, \tag{128}
--   $$
--
--   where $A=\|\mathbf a\|_1$. Moreover $b_h=0$ unless $A\ge h$ and $h+A$ is even.
--
--   These bounds give the contraction factor in Lemma 11 and the remainder estimates of Lemma 9.
--
--   **Formalization Note** $b_h$ is computed by (127); the entries of $\mathbf a$ are $\ge1$; the exponent $(h+A)/2$ is a real power; $C>0$.
--
--   Differences from the source:
--   - encoding: b_h the coefficient in Φ_a = Σ b_m P_m → b_h = N_h E_ρ[P_h(ρ) Π P_{a_i}(ρ)]; reason: the paper's identity (127)
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), Lemma 12, eq. (128), p.34 (PDF p.36)

import Mathlib
import Definitions.Def_RGGDetect_harmCoef

namespace RGGDetect

/-- **Lemma 12** (products of zonal polynomials; arXiv:2610.08517, held version, sha256 e7bebd4a…,
Lemma 12, p.34, eq. (128)): there is an absolute constant `C` such that for every `d ≥ 3`, `h ≥ 0`,
`k ≥ 1` and `a ∈ ℕ^k`,
`0 ≤ b_h/N_h ≤ min{1/N_{max{h, a₁, …, a_k}}, (C(h + A)/d)^{(h+A)/2}}`, `A = ‖a‖₁`.
Moreover `b_h = 0` unless `A ≥ h` and `h + A` is even.

**Formalization Note** `a : Fin k → ℕ` with entries `≥ 1` (`ℕ = {1, 2, …}`); `b_h` is `bCoef` with
`S` the whole index set, by (127); the exponent `(h + A)/2` is real. -/
theorem lemma_12 : ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 3 ≤ d → ∀ h k : ℕ, 1 ≤ k →
    ∀ a : Fin k → ℕ, (∀ j, 1 ≤ a j) →
      0 ≤ bCoef d h Finset.univ a / harmDim d h ∧
      bCoef d h Finset.univ a / harmDim d h ≤
        min (1 / (harmDim d (max h (Finset.univ.sup a)) : ℝ))
          ((C * ((h : ℝ) + ∑ j, (a j : ℝ)) / d) ^ (((h : ℝ) + ∑ j, (a j : ℝ)) / 2)) ∧
      (bCoef d h Finset.univ a ≠ 0 → h ≤ ∑ j, a j ∧ Even (h + ∑ j, a j)) := by sorry

end RGGDetect
