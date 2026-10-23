-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartIV_eq_16_2_4
-- name    : RamanujanLostNotebook.PartIV.eq_16_2_4
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T12:44:08.573499+00:00
-- url     : https://prove2.me/theorems/2d3528b7-974f-46ae-869d-b79bb99d9cef
-- title:
--   Closed form of phi(alpha,beta) phi(beta,alpha)
-- statement:
--   For $\alpha,\beta\in\mathbb C$ put $\varphi(\alpha,\beta)=\prod_{n\ge1}\{1+(\frac{\alpha+\beta}{n+\alpha})^3\}$. If none of $\alpha,\beta,\alpha+2\beta,\beta+2\alpha$ is a negative integer and $\alpha^2+\alpha\beta+\beta^2\ne0$, both products converge and $\varphi(\alpha,\beta)\varphi(\beta,\alpha)=\frac{\{\Gamma(1+\alpha)\Gamma(1+\beta)\}^3}{\Gamma(1+\alpha+2\beta)\Gamma(1+\beta+2\alpha)}\cdot\frac{\cosh(\pi(\alpha+\beta)\sqrt3)-\cos(\pi(\alpha-\beta))}{2\pi^2(\alpha^2+\alpha\beta+\beta^2)}$. Differs from the printed source: the book (p. 352) names no number field and no side conditions; here $\alpha,\beta\in\mathbb C$, the exclusions of (16.2.2) and (16.2.3) are assumed and convergence of both products is asserted (changes by us; numerical checks only).
--
--   **Discrepancy from the printed source.** The book prints (16.2.4), p. 352, with no number field and no side conditions, using the symbol phi. We state it for alpha, beta in C, add the pole and denominator exclusions of (16.2.2) and (16.2.3), and make convergence of the two products phi(alpha,beta), phi(beta,alpha) part of the conclusion instead of introducing phi as a definition. Evidence: numerical agreement of both sides at the sample points listed in notes (real and non-real, including points next to the excluded ones); numerical evidence, not a proof. Change made by us, not by the book's authors.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 16, Entry 16.2.4, p. 352, eq. (16.2.4).

import Mathlib

namespace RamanujanLostNotebook.PartIV
theorem eq_16_2_4 (α β : ℂ)
    (hα : ∀ n : ℕ, α ≠ -((n : ℂ) + 1)) (hβ : ∀ n : ℕ, β ≠ -((n : ℂ) + 1))
    (hαβ : ∀ n : ℕ, α + 2 * β ≠ -((n : ℂ) + 1))
    (hβα : ∀ n : ℕ, β + 2 * α ≠ -((n : ℂ) + 1))
    (h : α ^ 2 + α * β + β ^ 2 ≠ 0) :
    ∃ P Q : ℂ,
      HasProd (fun n : ℕ => 1 + ((α + β) / (((n : ℂ) + 1) + α)) ^ 3) P ∧
      HasProd (fun n : ℕ => 1 + ((α + β) / (((n : ℂ) + 1) + β)) ^ 3) Q ∧
      P * Q =
        (Complex.Gamma (1 + α) * Complex.Gamma (1 + β)) ^ 3
            / (Complex.Gamma (1 + α + 2 * β) * Complex.Gamma (1 + β + 2 * α))
          * ((Complex.cosh ((Real.pi : ℂ) * (α + β) * (Real.sqrt 3 : ℂ))
                - Complex.cos ((Real.pi : ℂ) * (α - β)))
              / (2 * (Real.pi : ℂ) ^ 2 * (α ^ 2 + α * β + β ^ 2))) := by sorry
end RamanujanLostNotebook.PartIV
