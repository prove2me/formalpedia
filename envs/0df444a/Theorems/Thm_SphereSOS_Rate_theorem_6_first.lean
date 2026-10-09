-- Prove2me | Theorems.Thm_SphereSOS_Rate_theorem_6_first
-- name    : SphereSOS.Rate.theorem_6_first
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:20:04.859456+00:00
-- url     : https://prove2.me/theorems/5ff33cb3-ab39-4462-adbe-51dcf0351700
-- title:
--   Theorem 6 (first part), p. 7 — $F+\frac{B_{2n}}2\sum_{k=1}^n|\lambda_{2k}^{-1}-1|\,I$ is $\ell$-sos for every admissible $q$
-- statement:
--   Let $d\ge2$. Let $F$ be a $k\times k$ matrix polynomial in $d$ variables, homogeneous of degree $2n$, with $F(x)$ symmetric for all $x$ and $0\preceq F(x)\preceq I$ for all $x\in S^{d-1}$. Let $B$ be a Proposition 5 bound in dimension $d$ (for instance $B_{2n}$). Let $q$ be a univariate polynomial of degree at most $\ell$ whose square $\phi=q^2$ has Gegenbauer coefficients with $\lambda_0=1$ and $\lambda_{2k}\ne0$ for $k=1,\dots,n$. Then
--   $$F+\frac B2\sum_{k=1}^n\big|\lambda_{2k}^{-1}-1\big|\;I\quad\text{is }\ell\text{-sos on }S^{d-1}.$$
--
--   Minimizing over $q$ gives the printed statement: $F+(B_{2n}/2)\rho_{2n}(d,\ell)I$ is $\ell$-sos on $S^{d-1}$. Together with the second part this proves Theorem 2.
--
--   **Formalization Note** This is the statement the proof establishes at (12), with $\delta=(B_{2n}/2)\sum_k|\lambda_{2k}^{-1}-1|$. It is posed per $q$ (and per bound $B$) to avoid a real infimum; it implies the printed form because the minimum defining $\rho_{2n}$ is attained and adding $cI$, $c\ge0$, preserves $\ell$-sos. The hypothesis $\lambda_{2k}\ne0$ is the finiteness of $|\lambda_{2k}^{-1}-1|$ (Lean's $0^{-1}=0$ would otherwise give a false finite value). $d\ge2$ is the standing assumption of §2–3.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 7, Theorem 6 (first part), its proof, (12), and the paragraph 'Matrix-valued polynomials'

import Mathlib
import Definitions.Def_SphereSOS_Rate_Setting
import Definitions.Def_SphereSOS_Rate_Gegenbauer

namespace SphereSOS.Rate

theorem theorem_6_first (n d k ℓ : ℕ) (B : ℝ)
    (q : Polynomial ℝ)
    (F : Matrix (Fin k) (Fin k) (MvPolynomial (Fin d) ℝ))
    (hd : 2 ≤ d)
    (hB : PropFiveBound n d B)
    (hqdeg : q.natDegree ≤ ℓ)
    (hqnorm : gegCoeff d (q ^ 2) 0 = 1)
    (hqnonzero : ∀ j ∈ Finset.Icc 1 n, gegCoeff d (q ^ 2) (2 * j) ≠ 0)
    (hdeg : ∀ a b, (F a b).IsHomogeneous (2 * n))
    (hsymm : ∀ x, (evalM x F).IsSymm)
    (hbound : ∀ x ∈ sphere d,
      (evalM x F).PosSemidef ∧ (1 - evalM x F).PosSemidef) :
    IsSosOnSphere ℓ
      (F + (((B / 2) *
        ∑ j ∈ Finset.Icc 1 n,
          |(gegCoeff d (q ^ 2) (2 * j))⁻¹ - 1|) : ℝ) •
            (1 : Matrix (Fin k) (Fin k) (MvPolynomial (Fin d) ℝ))) := by sorry

end SphereSOS.Rate
