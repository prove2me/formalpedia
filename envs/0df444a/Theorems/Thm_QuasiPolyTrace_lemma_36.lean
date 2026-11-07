-- Prove2me | Theorems.Thm_QuasiPolyTrace_lemma_36
-- name    : QuasiPolyTrace.lemma_36
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:31:52.152279+00:00
-- url     : https://prove2.me/theorems/6c47413f-44e0-4d7a-977d-648cf03c564f
-- title:
--   Lemma 36 — a summed triple product becomes one smoothly weighted statistic
-- statement:
--   Let $x,y$ be binary strings and $p\in(0,\tfrac14]$. Let $w:\mathbb Z\to\mathbb R_{\ge0}$ be supported on $[I_-,I_+]$ with $1\le I_-\le I_+$ integers, $\sum_jw(j)\le1$, and Fourier transform of magnitude $\le\delta$ at every angle $\xi\in(-\pi,\pi]$ with $|\xi|\ge\varepsilon$, where $\varepsilon\in(0,\tfrac13p]$. Let $s$ be a set of $k$ positive integers with $\min s=1$ and $\sigma=\max s$, let $\ell_1,\ell_2\ge0$ be integers, put $f(j)=w(j)x^{(s+j)}_p$, $g(j)=w(j)y^{(s+j)}_p$, and suppose for some $\tau>0$ that
--
--   $$
--   \Big|\sum_j f(j)f(j+\ell_1)f(j+\ell_2)-g(j)g(j+\ell_1)g(j+\ell_2)\Big|\ge\tau
--   \quad\text{or}\quad
--   \Big|\sum_j f(j)f(j+\ell_1)-g(j)g(j+\ell_1)\Big|\ge\tau .
--   $$
--
--   Let $\lambda=3I_++\ell_1+\ell_2$. Then there are $P\in[p,3p]$, a set $S$ of at most $3k$ positive integers with $\min S=1$ and $\max S\le10(I_++\sigma)$, and $A:\mathbb Z\to\mathbb R_{\ge0}$ supported in $[I_-,\lambda]$ with $\sum_jA(j)\le1$, whose Fourier transform has magnitude at most
--
--   $$
--   300(I_++\sigma)^2\Big(\lambda\delta+\max\big(\lambda,\tfrac{8\pi}{3\varepsilon}\big)e^{-\varepsilon I_-/4}\Big)
--   $$
--
--   at every angle $\xi\in(-\pi,\pi]$ with $|\xi|>9\varepsilon$, such that
--
--   $$
--   \Big|\sum_jA(j)\big(x^{(S+j)}_P-y^{(S+j)}_P\big)\Big|\ \ge\ \frac{\tau-3\cdot2^{-I_+}}{(10(I_++\sigma))^{3k}} .
--   $$
--
--   Differences from the source:
--   - encoding: k-tuple of distinct positive integers s, min 1, σ = max → finite set s of integers ≥ 1 with 1 ∈ s, σ its greatest element, k = |s|; S likewise; reason: distinct entries make a tuple a set; bits are 0/1
--   - reading: positive integer interval [I₋, I₊]; frequencies |ξ| ≥ ε; frequencies greater than 9ε → 1 ≤ I₋ ≤ I₊; angles ξ ∈ (−π, π] with ε ≤ |ξ|; angles with 9ε < |ξ|; reason: the Fourier transform is a function of an angle in (−π, π] (Definition 4); "greater than" is read strictly, as printed
-- source:
--   Burudgunte, Valiant, Wang, Quasipolynomial Trace Reconstruction, manuscript of November 2, 2026 (later version of arXiv:2607.04073; sha256 9ecb6d18…), Lemma 36, p.32

import Mathlib
import Definitions.Def_QuasiPolyTrace_stat
import Definitions.Def_QuasiPolyTrace_shift
import Definitions.Def_QuasiPolyTrace_fourier

namespace QuasiPolyTrace

open scoped Real

/-- **Lemma 36 (a summed triple product becomes one smoothly weighted statistic).** Burudgunte, Valiant, Wang, *Quasipolynomial Trace Reconstruction*, manuscript of November 2, 2026
(later version of arXiv:2607.04073; sha256 9ecb6d18…), Lemma 36,
p.32: "Let x, y be two binary strings and let p ∈ (0, ¼] be a retention probability. Suppose there is a
weight function w : Z → R≥0 supported on a positive integer interval [I₋, I₊], having sum ≤ 1, and for
frequencies |ξ| ≥ ε has Fourier transform of magnitude ≤ δ, for ε ∈ (0, ⅓p]. Suppose there is a k-tuple of
distinct positive integers s with min_i s_i = 1 and σ := max_i s_i such that, we have three offsets
ℓ₀ = 0, ℓ₁, ℓ₂ ≥ 0 where, defining f(j) := w(j)x^{(s+j)}_p and g(j) := w(j)y^{(s+j)}_p, we suppose, for
some τ > 0 that |∑_j f(j)f(j + ℓ₁)f(j + ℓ₂) − g(j)g(j + ℓ₁)g(j + ℓ₂)| ≥ τ or
|∑_j f(j)f(j+ℓ₁) − g(j)g(j+ℓ₁)| ≥ τ. Defining λ = 3I₊ + ℓ₀ + ℓ₁ + ℓ₂ then: there exists a probability
P ∈ [p, 3p], a tuple S of ≤ 3k distinct positive integers having minimum value 1 and maximum value
≤ 10(I₊ + σ), and there exists a weight function A : Z → R≥0 that is supported within [I₋, λ], sums to
≤ 1, and where A has Fourier transform of magnitude ≤ 300(I₊ + σ)² · (λδ + max(λ, 8π/(3ε)) · e^{−εI₋/4})
at frequencies greater than 9ε such that |∑_j A(j)(x^{(S+j)}_P − y^{(S+j)}_P)| ≥
(τ − 3·2^{−I₊})/(10(I₊ + σ))^{3k}."

**Formalization Note.**
* `x`, `y` are arbitrary binary strings (lists; their lengths need not agree).
* Statistics are finite sets of integers; `s + j` is `shift s j`. "k-tuple of distinct positive integers
  with min 1 and max σ" is: `1 ∈ s`, every entry `≥ 1`, `σ` the greatest entry, `k = |s|`.
* "positive integer interval [I₋, I₊]" is `1 ≤ I₋ ≤ I₊`.
* Fourier transforms are those of Definition 4 at angles `ξ ∈ (−π, π]`; "frequencies |ξ| ≥ ε" means
  `ε ≤ |ξ|`, and "frequencies greater than 9ε" means `9ε < |ξ|`.
* `w` and `A` are finitely supported, so all sums over `ℤ` are finite sums. -/
theorem lemma_36 (x y : List Bool) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1 / 4)
    (w : ℤ → ℝ) (Im Ip : ℤ) (hIm : 1 ≤ Im) (hI : Im ≤ Ip) (hw0 : ∀ j, 0 ≤ w j)
    (hws : ∀ j, w j ≠ 0 → Im ≤ j ∧ j ≤ Ip) (hw1 : ∑' j, w j ≤ 1)
    (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ p / 3)
    (hwF : ∀ ξ : ℝ, -π < ξ → ξ ≤ π → ε ≤ |ξ| → ‖fourier (fun j => ((w j : ℝ) : ℂ)) ξ‖ ≤ δ)
    (s : Finset ℤ) (hs1 : 1 ∈ s) (hspos : ∀ i ∈ s, 1 ≤ i) (σ : ℤ) (hσ : IsGreatest (s : Set ℤ) σ)
    (ℓ₁ ℓ₂ : ℤ) (hℓ₁ : 0 ≤ ℓ₁) (hℓ₂ : 0 ≤ ℓ₂) (τ : ℝ) (hτ : 0 < τ)
    (hdisc :
      τ ≤ |∑' j : ℤ, (w j * stat p x (shift s j) * (w (j + ℓ₁) * stat p x (shift s (j + ℓ₁)))
            * (w (j + ℓ₂) * stat p x (shift s (j + ℓ₂)))
          - w j * stat p y (shift s j) * (w (j + ℓ₁) * stat p y (shift s (j + ℓ₁)))
            * (w (j + ℓ₂) * stat p y (shift s (j + ℓ₂))))| ∨
      τ ≤ |∑' j : ℤ, (w j * stat p x (shift s j) * (w (j + ℓ₁) * stat p x (shift s (j + ℓ₁)))
          - w j * stat p y (shift s j) * (w (j + ℓ₁) * stat p y (shift s (j + ℓ₁))))|) :
    ∃ P : ℝ, p ≤ P ∧ P ≤ 3 * p ∧
      ∃ S : Finset ℤ, S.card ≤ 3 * s.card ∧ 1 ∈ S ∧ (∀ i ∈ S, 1 ≤ i ∧ i ≤ 10 * (Ip + σ)) ∧
      ∃ A : ℤ → ℝ, (∀ j, 0 ≤ A j) ∧ (∀ j, A j ≠ 0 → Im ≤ j ∧ j ≤ 3 * Ip + 0 + ℓ₁ + ℓ₂) ∧
        ∑' j, A j ≤ 1 ∧
        (∀ ξ : ℝ, -π < ξ → ξ ≤ π → 9 * ε < |ξ| →
          ‖fourier (fun j => ((A j : ℝ) : ℂ)) ξ‖ ≤
            300 * ((Ip + σ : ℤ) : ℝ) ^ 2 * (((3 * Ip + 0 + ℓ₁ + ℓ₂ : ℤ) : ℝ) * δ
              + max ((3 * Ip + 0 + ℓ₁ + ℓ₂ : ℤ) : ℝ) (8 * π / (3 * ε)) * Real.exp (-ε * Im / 4))) ∧
        (τ - 3 * (2 : ℝ) ^ (-Ip)) / (10 * ((Ip + σ : ℤ) : ℝ)) ^ (3 * s.card) ≤
          |∑' j : ℤ, A j * (stat P x (shift S j) - stat P y (shift S j))| := by sorry

end QuasiPolyTrace
