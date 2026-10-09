-- Prove2me | Theorems.Thm_SphereSOS_Rate_lemma_16
-- name    : SphereSOS.Rate.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:19:57.335063+00:00
-- url     : https://prove2.me/theorems/73bc8d45-3689-43b8-ad19-e9125c373865
-- title:
--   Lemma 16, p. 15 — $\|\Delta^k f\|_\infty\le d^k(n)_{2k}\|f\|_\infty$ for homogeneous $f$ of degree $n$
-- statement:
--   Let $f$ be a real homogeneous polynomial of degree $m$ in $d$ variables, and let $M$ be such that $|f(x)|\le M$ for all $x\in S^{d-1}$. Then for every $j\ge0$,
--   $$|\Delta^jf(x)|\le d^{\,j}\,(m)_{2j}\,M\qquad\text{for all }x\in S^{d-1},$$
--   where $\Delta$ is the Laplacian and $(m)_r=m(m-1)\cdots(m-r+1)$ is the falling factorial.
--
--   This is Reznick's bound on iterated Laplacians in the sup norm on the sphere; it is the input that makes the harmonic component bound of Proposition 5 independent of the dimension.
--
--   **Formalization Note** The paper names the degree $n$ and the exponent $k$; here they are $m$ and $j$. $\|f\|_\infty\le M$ is stated pointwise on the sphere. $(m)_{2j}=0$ when $2j>m$, in agreement with $\Delta^jf=0$.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 15, Lemma 16 (quoted from [Rez95])

import Mathlib
import Definitions.Def_SphereSOS_Rate_Setting

namespace SphereSOS.Rate

theorem lemma_16 (d m j : ℕ) (f : MvPolynomial (Fin d) ℝ) (M : ℝ)
    (hf : f.IsHomogeneous m)
    (hM : ∀ x ∈ sphere d, |MvPolynomial.eval x f| ≤ M) :
    ∀ x ∈ sphere d,
      |MvPolynomial.eval x ((laplacian^[j]) f)| ≤
        (d : ℝ) ^ j * (m.descFactorial (2 * j) : ℝ) * M := by sorry

end SphereSOS.Rate
