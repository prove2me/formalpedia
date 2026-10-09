-- Prove2me | Theorems.Thm_RamanujanNotebooks_entry_4_10
-- name    : RamanujanNotebooks.entry_4_10
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T21:48:54.311415+00:00
-- url     : https://prove2.me/theorems/609105a0-7c96-4549-82e0-1c8b24868c43
-- title:
--   Σ C(n,k) φ(k) = Σ C(n,k) φ(n-k) under a contour-integral hypothesis
-- statement:
--   Let $n\in\mathbb C$ with $2n\notin\mathbb Z$, let $\varphi$ be entire, and let $r_j>0$, $r_j\to\infty$, be radii with $r_j\notin\mathbb Z$ and $r_j\ne|n-m|$ for all integers $m$, such that $\frac1{2\pi i}\oint_{|z|=r_j}\frac{\pi\varphi(z)\cot(\pi z)\cot\{\pi(z-n)\}}{\Gamma(z+1)\Gamma(n-z+1)}dz\to0$. If $\sum_{k\ge0}\binom nk\varphi(k)$ and $\sum_{k\ge0}\binom nk\varphi(n-k)$ both converge, then they are equal. Differs from the printed source: the book states this for every complex $n$; it is false for $n$ half an odd integer (there the integrand is entire, so the hypothesis always holds, but for $n=\tfrac12$, $\varphi(z)=2^z\sin(\pi z)$ the sums are $0$ and $1$), and the book's residue computation needs $2n\notin\mathbb Z$; this hypothesis and the avoidance of the poles by the contours are added by us (exact counterexample; correction ours).
--
--   **Discrepancy from the printed source.** Book p. 100, Entry 10: 'Let n be complex and let φ be an entire function …', proof says the case of nonnegative integers n is trivial and assumes the contrary. (a) For n = m + 1/2 the product cot(πz) cot(π(z - n)) is identically -1, the integrand is entire and I_j = 0 for every entire φ; with n = 1/2, φ(z) = 2^z sin(πz) both series converge, to 0 and to 1: the printed statement is false there (exact counterexample; also checked numerically). (b) The residues carry the factor cot(πn), by which the proof divides, and are computed for simple poles, which fails for integer n. Stated here with 2n ∉ ℤ and with contours avoiding the poles. Correction ours. Confirmed by the independent Codex audit (AUDIT_codex.md, section A): for n = 1/2, φ(z) = 2^z sin(πz) the first series is 0 termwise and the partial sums of the second at 30, 60, 100 terms are 1 + 4.37e-12, 1 + 1.46e-21, 1 + 6.2e-34; cot(πz) cot(π(z - 1/2)) = -1. The nonnegative-integer case is entry_4_10_nat (added at the audit's request); negative integers n are not treated.
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
