-- Prove2me | Theorems.Thm_SphereSOS_Rate_proposition_17
-- name    : SphereSOS.Rate.proposition_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:20:26.018169+00:00
-- url     : https://prove2.me/theorems/793be1d6-606d-4454-9e70-fcddd745a7d3
-- title:
--   Proposition 17, p. 16 — $\|F_{2k}\|_\infty\le B_{2n}\|F\|_\infty$ for symmetric matrix polynomials (spectral norm)
-- statement:
--   Let $F$ be a $k\times k$ matrix polynomial in $d$ variables, homogeneous of degree $2n$, with $F(x)$ symmetric for every $x$, and let $F=\sum_{j=0}^n\|x\|^{2(n-j)}F_{2j}$ be its (entrywise) harmonic decomposition. Let $B$ be a Proposition 5 bound in dimension $d$ (for instance $B_{2n}$). If $\|F(x)\|\le M$ for all $x\in S^{d-1}$, where $\|\cdot\|$ is the spectral norm, then
--   $$\|F_{2j}(x)\|\le B\,M\qquad\text{for all }x\in S^{d-1},\ j=0,\dots,n.$$
--
--   This lifts the scalar estimate to matrices with no dependence on $k$; it is the bound used in the matrix case of Theorem 6.
--
--   **Formalization Note** The spectral norm of a symmetric matrix $A$ is written $\max_{\|y\|=1}|y^{\mathsf T}Ay|$ (the paper's proof uses exactly this); hypothesis and conclusion are stated for all unit vectors $y\in\mathbb R^k$. The $F_{2j}$ are symmetric because the decomposition is unique. Homogeneity of $F$ is explicit: the page says "of degree $2n$", and the proof applies Proposition 5, which is about homogeneous polynomials, to $y^{\mathsf T}F(\cdot)y$.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 16, Proposition 17

import Mathlib
import Definitions.Def_SphereSOS_Rate_Setting

namespace SphereSOS.Rate

theorem proposition_17 (n d k : ℕ) (B M : ℝ)
    (F : Matrix (Fin k) (Fin k) (MvPolynomial (Fin d) ℝ))
    (H : Fin (n + 1) → Matrix (Fin k) (Fin k) (MvPolynomial (Fin d) ℝ))
    (hB : PropFiveBound n d B)
    (hdeg : ∀ a b, (F a b).IsHomogeneous (2 * n))
    (hsymm : ∀ x, (evalM x F).IsSymm)
    (hdecomp : ∀ a b, IsHarmonicDecomp n (F a b) (fun j => H j a b))
    (hM : ∀ x ∈ sphere d, ∀ y : Fin k → ℝ,
      (∑ i, y i ^ 2) = 1 → |dotProduct y (Matrix.mulVec (evalM x F) y)| ≤ M) :
    ∀ j x, x ∈ sphere d → ∀ y : Fin k → ℝ,
      (∑ i, y i ^ 2) = 1 → |dotProduct y (Matrix.mulVec (evalM x (H j)) y)| ≤ B * M := by sorry

end SphereSOS.Rate
