-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_lemma_3_3
-- name    : SpikedWishart.SoftEdge.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:39:21.213308+00:00
-- url     : https://prove2.me/theorems/beb91594-4d0d-4741-99f5-c1269838aec1
-- title:
--   Lemma 3.3, p. 1677 — F_k is well defined (its Fredholm series converges) and s^{(m)} has the closed form (203)
-- statement:
--   Let $K_k(u,v)=A(u,v)+\sum_{m=1}^k s^{(m)}(u)\,t^{(m)}(v)$ be the kernel whose Fredholm determinant on $L^2((x,\infty))$ is $F_k(x)$. Then:
--
--   1. **$F_k$ is well defined.** For every $k\ge0$ and real $x$, each integrand $(u_1,\dots,u_n)\mapsto\det[K_k(u_i,u_j)]_{i,j=1}^n$ is integrable on $(x,\infty)^n$, and the Fredholm series
--   $$
--   \sum_{n=0}^\infty\frac{(-1)^n}{n!}\int_{(x,\infty)^n}\det[K_k(u_i,u_j)]\,du
--   $$
--   converges absolutely.
--   2. **Formula (203).** For every $m\ge1$ and real $u$,
--   $$
--   s^{(m)}(u)=\sum_{\ell+3n=m-1}\frac{(-1)^n}{3^n\,\ell!\,n!}u^\ell+\frac1{(m-1)!}\int_\infty^u(u-y)^{m-1}\mathrm{Ai}(y)\,dy ,
--   $$
--   with $\int_\infty^u=-\int_u^\infty$ and the sum over $\ell,n\ge0$.
--
--   The functions $s^{(m)}$ grow polynomially, so part 1 is a genuine statement: it rests on the super-exponential decay of $A$ and $t^{(m)}$.
--
--   **Formalization Note** The paper's "well defined" refers to the inner products $\langle(1-A_x)^{-1}s^{(m)},t^{(n)}\rangle$ of (17); with $F_k$ defined through the Fredholm series of (201), its formal content is the integrability and absolute summability stated here. The paper's (15) prints the integral term inside the sum; (203), stated here, has it outside.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1677, Lemma 3.3, (203)

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Airy
open MeasureTheory

namespace SpikedWishart.SoftEdge

theorem lemma_3_3 :
    (∀ (k : ℕ) (x : ℝ),
      (∀ n : ℕ, IntegrableOn (fun u : Fin n → ℝ => (Matrix.of fun i j => kernelFk k (u i) (u j)).det)
        (Set.pi Set.univ (fun _ : Fin n => Set.Ioi x))) ∧
      Summable (fun n : ℕ => |((-1 : ℝ) ^ n / (n.factorial : ℝ)) *
        ∫ u in Set.pi Set.univ (fun _ : Fin n => Set.Ioi x),
          (Matrix.of fun i j : Fin n => kernelFk k (u i) (u j)).det|)) ∧
    ∀ (m : ℕ), 1 ≤ m → ∀ u : ℝ,
      sFn m u =
        (∑ n ∈ Finset.range ((m - 1) / 3 + 1),
            (-1 : ℝ) ^ n / (3 ^ n * ((m - 1 - 3 * n).factorial * n.factorial)) * u ^ (m - 1 - 3 * n)) -
          (1 / ((m - 1).factorial : ℝ)) * ∫ y in Set.Ioi u, (u - y) ^ (m - 1) * Ai y := by sorry

end SpikedWishart.SoftEdge
