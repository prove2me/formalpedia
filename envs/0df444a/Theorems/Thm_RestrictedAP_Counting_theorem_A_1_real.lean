-- Prove2me | Theorems.Thm_RestrictedAP_Counting_theorem_A_1_real
-- name    : RestrictedAP.Counting.theorem_A_1_real
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:06:55.865972+00:00
-- url     : https://prove2.me/theorems/db106010-85ce-4477-af21-5590322bcfb2
-- title:
--   Theorem A.1 — multidimensional Gaussian reverse hypercontractivity (real form)
-- statement:
--   Let $\ell \in \mathbb N$, let $\iota$ be a finite nonempty index set, and let $\eta > 0$. Let $B$ be a real square matrix indexed by $[\ell] \times \iota$. Let $G = Bz$, where $z$ is a standard Gaussian vector with independent $N(0,1)$ coordinates indexed by $[\ell] \times \iota$. Write $G_j = (G_{(j,k)})_{k \in \iota}$. Assume:
--
--   - each diagonal block of the covariance $P = BB^{\mathsf T}$ is the identity, so each $G_j$ is a vector of independent $N(0,1)$ Gaussians;
--   - $P - \eta I$ is positive semidefinite.
--
--   Then for all measurable $f_1, \dots, f_\ell : \mathbb R^\iota \to [0,1]$ with $\mathbb E f_j(G_j) = \mu_j$,
--   $$\mathbb E\Big[\prod_{j=1}^{\ell} f_j(G_j)\Big] \ge \Big(\prod_{j=1}^{\ell} \mu_j\Big)^{1/\eta}.$$
--
--   The paper (Appendix A, p. 53) states this as Theorem A.1, citing W.-K. Chen, N. Dafnis and G. Paouris, *Improved Hölder and reverse Hölder inequalities for Gaussian random vectors*, Adv. Math. 280 (2015) 643–689 ([doi:10.1016/j.aim.2014.09.029](https://doi.org/10.1016/j.aim.2014.09.029)), and J. Hązła, T. Holenstein and E. Mossel, *Product space models of correlation: between noise stability and additive combinatorics*, Discrete Analysis 2018. Here the jointly Gaussian collection is written as a linear image $Bz$ of a standard Gaussian vector; every centred Gaussian vector has this form.
--
--   The paper derives its complex Theorem 5.11 (`RestrictedAP.Counting.theorem_5_11`) from this by realification. Writing $G_j = X_j + iY_j$ and $\tilde G_j = \sqrt 2\,(X_j, Y_j)$, the real covariance is the blockwise realification of $P$. That realification keeps the lower bound $\eta$.
-- source:
--   Amey Bhangale, Subhash Khot, Yang P. Liu and Dor Minzer, A Counting Lemma for Somewhat Restricted 3-APs, ACM STOC 2027 submission 1020, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1020.pdf, p. 53, Theorem A.1 (the real multidimensional Gaussian reverse hypercontractivity theorem the paper cites from Chen–Dafnis–Paouris, Adv. Math. 280 (2015) 643–689, and Hązła–Holenstein–Mossel, Discrete Analysis 2018)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace RestrictedAP.Counting

theorem theorem_A_1_real (ℓ : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (η : ℝ) (hη : 0 < η)
    (B : Matrix (Fin ℓ × ι) (Fin ℓ × ι) ℝ)
    (hblock : ∀ (j : Fin ℓ) (k k' : ι),
      (B * B.transpose) (j, k) (j, k') = if k = k' then 1 else 0)
    (hcov : (B * B.transpose - η • (1 : Matrix (Fin ℓ × ι) (Fin ℓ × ι) ℝ)).PosSemidef)
    (f : Fin ℓ → (ι → ℝ) → ℝ) (hf : ∀ j, Measurable (f j))
    (hf01 : ∀ j x, 0 ≤ f j x ∧ f j x ≤ 1) :
    let law : Measure (Fin ℓ × ι → ℝ) :=
      (Measure.pi (fun _ : Fin ℓ × ι => gaussianReal 0 1)).map (fun z => B.mulVec z)
    (∏ j, ∫ g, f j (fun k => g (j, k)) ∂law) ^ (1 / η) ≤
      ∫ g, ∏ j, f j (fun k => g (j, k)) ∂law := by sorry

end RestrictedAP.Counting
