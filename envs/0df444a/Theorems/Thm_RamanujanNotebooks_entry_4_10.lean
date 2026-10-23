-- Prove2me | Theorems.Thm_RamanujanNotebooks_entry_4_10
-- name    : RamanujanNotebooks.entry_4_10
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T21:48:54.311415+00:00
-- url     : https://prove2.me/theorems/609105a0-7c96-4549-82e0-1c8b24868c43
-- title:
--   Σ C(n,k) φ(k) = Σ C(n,k) φ(n-k) under a contour-integral hypothesis
-- statement:
--   Let $n\in\mathbb C$ with $2n\notin\mathbb Z$, let $\varphi$ be entire, and let $r_j>0$, $r_j\to\infty$, be radii with $r_j\notin\mathbb Z$ and $r_j\ne|n-m|$ for all integers $m$, such that $\frac1{2\pi i}\oint_{|z|=r_j}\frac{\pi\varphi(z)\cot(\pi z)\cot\{\pi(z-n)\}}{\Gamma(z+1)\Gamma(n-z+1)}dz\to0$. If $\sum_{k\ge0}\binom nk\varphi(k)$ and $\sum_{k\ge0}\binom nk\varphi(n-k)$ both converge, then they are equal. Entry 10 on p. 100 permits unrestricted complex $n$. This version excludes $2n\in\mathbb Z$ and requires every contour to avoid both pole sets. The residue calculation uses simple poles and cancels the nonzero factor $\cot(\pi n)$; these steps require the added restriction.
--
--   **Discrepancy from the printed source.** For $n=1/2$ and $\varphi(z)=2^z\sin(\pi z)$, the first series vanishes termwise and the second sums to $1$. Meanwhile $\cot(\pi z)\cot(\pi(z-1/2))=-1$, and the reciprocal Gamma factors extend the integrand to an entire function, so its circular integrals vanish. Thus the unrestricted conclusion fails. Nonnegative integral $n$ instead gives a finite identity without these hypotheses and is stated separately; negative integral $n$ is outside this formulation.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 4, Entry 10, p. 100.

import Mathlib

namespace RamanujanNotebooks
theorem entry_4_10 (n : ℂ) (hn : ∀ m : ℤ, 2 * n ≠ (m : ℂ)) (φ : ℂ → ℂ)
    (hφ : Differentiable ℂ φ) (r : ℕ → ℝ)
    (hr0 : ∀ j : ℕ, 0 < r j) (hr : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hint : ∀ j m : ℕ, r j ≠ (m : ℝ)) (hshift : ∀ (j : ℕ) (m : ℤ), r j ≠ ‖n - (m : ℂ)‖)
    (hI : Filter.Tendsto
      (fun j : ℕ => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        circleIntegral (fun z : ℂ => (Real.pi : ℂ) * φ z *
          (Complex.cos ((Real.pi : ℂ) * z) / Complex.sin ((Real.pi : ℂ) * z)) *
          (Complex.cos ((Real.pi : ℂ) * (z - n)) / Complex.sin ((Real.pi : ℂ) * (z - n))) /
          (Complex.Gamma (z + 1) * Complex.Gamma (n - z + 1))) 0 (r j))
      Filter.atTop (nhds 0))
    (s t : ℂ)
    (hs : Filter.Tendsto
      (fun K : ℕ => ∑ k ∈ Finset.range K,
        (∏ i ∈ Finset.range k, (n - (i : ℂ))) / (k.factorial : ℂ) * φ (k : ℂ))
      Filter.atTop (nhds s))
    (ht : Filter.Tendsto
      (fun K : ℕ => ∑ k ∈ Finset.range K,
        (∏ i ∈ Finset.range k, (n - (i : ℂ))) / (k.factorial : ℂ) * φ (n - (k : ℂ)))
      Filter.atTop (nhds t)) :
    s = t := by sorry
end RamanujanNotebooks
