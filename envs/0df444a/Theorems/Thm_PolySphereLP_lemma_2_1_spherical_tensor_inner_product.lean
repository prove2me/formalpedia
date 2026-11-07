-- Prove2me | Theorems.Thm_PolySphereLP_lemma_2_1_spherical_tensor_inner_product
-- name    : PolySphereLP.lemma_2_1_spherical_tensor_inner_product
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:58:32.867035+00:00
-- url     : https://prove2.me/theorems/ac36ae1a-89f4-407f-83cf-0a1785ac68a2
-- title:
--   Lemma 2.1 — spherical and tensor inner products
-- statement:
--   Let $n\ge2$, let $k\ge0$ be an integer, let $\sigma$ be the uniform probability measure on $S^{n-1}$, and put $\mathrm R_{n,k}=\prod_{j=0}^{k-1}(n+2j)$.
--   1. If $G$ is a real or complex homogeneous harmonic polynomial of degree $k$, then
--   $$\|G\|^2_{L^2(\sigma)}=\frac{k!}{\mathrm R_{n,k}}\,\|T_G\|_F^2. \tag{25}$$
--   2. If $A$ is any homogeneous polynomial of degree $k$ and $B$ is a homogeneous harmonic polynomial of degree $k$, both possibly complex, then
--   $$\int A(x)\overline{B(x)}\,d\sigma(x)=\frac{k!}{\mathrm R_{n,k}}\,\langle T_A,T_B\rangle_F. \tag{26}$$
--
--   Only one of the two polynomials needs to be harmonic in the mixed identity. The identity converts spherical $L^2$ norms of harmonics into Frobenius norms of their coefficient tensors.
--
--   **Formalization Note** Stated for complex coefficients; real polynomials are the case of real coefficients. Points of the sphere are real and evaluated in $\mathbb C$.
--
--   Differences from the source:
--   - encoding: G real or complex → G with complex coefficients; reason: a real polynomial is a complex one with real coefficients, with the same values on ℝⁿ and the same tensor
--   - encoding: ‖G‖²_{L²(σ)} → ∫ |G(x)|² dσ(x); reason: definition of the L² norm
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), Lemma 2.1, p.12, eqs. (25)–(26)

import Mathlib
import Definitions.Def_SphereSOS_Rate_SphereMeasure
import Definitions.Def_PolySphereLP_Rmom
import Definitions.Def_PolySphereLP_harmonicSpaceC
import Definitions.Def_PolySphereLP_coeffTensor
open MvPolynomial MeasureTheory

namespace PolySphereLP

/-- **Lemma 2.1 (Spherical and tensor inner products).** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), Lemma 2.1, p.12, eqs. (25)–(26).

Let `n ≥ 2`, `k ≥ 0`, `σ` uniform on `S^{n−1}`, `R_{n,k} = ∏_{j<k}(n+2j)`. If `G` is a (real or
complex) homogeneous harmonic polynomial of degree `k`, then `‖G‖²_{L²(σ)} = (k!/R_{n,k}) ‖T_G‖²_F`
(25). If `A` is any homogeneous polynomial of degree `k` and `B` a homogeneous harmonic polynomial of
degree `k`, both possibly complex, then `∫ A(x) B̄(x) dσ(x) = (k!/R_{n,k}) ⟨T_A, T_B⟩_F` (26).

**Formalization Note.** Stated for complex coefficients; a real polynomial is the special case of
real coefficients (its complex image has the same values on `ℝⁿ` and the same tensor). Points of the
sphere are real, evaluated through `ℝ → ℂ`. `⟨S,T⟩_F = ∑ S·T̄` is linear in the first slot. -/
theorem lemma_2_1_spherical_tensor_inner_product (n : ℕ) (hn : 2 ≤ n) (k : ℕ) :
    (∀ G ∈ harmonicSpaceC n k,
      ∫ x, Complex.normSq (eval (fun i => (x i : ℂ)) G) ∂(SphereSOS.Rate.sigma n) =
        (k.factorial : ℝ) / Rmom n k * frobNormSq (coeffTensor k G)) ∧
    (∀ A B : MvPolynomial (Fin n) ℂ, A.IsHomogeneous k → B ∈ harmonicSpaceC n k →
      ∫ x, eval (fun i => (x i : ℂ)) A * starRingEnd ℂ (eval (fun i => (x i : ℂ)) B)
          ∂(SphereSOS.Rate.sigma n) =
        (((k.factorial : ℝ) / Rmom n k : ℝ) : ℂ) * frob (coeffTensor k A) (coeffTensor k B)) := by sorry

end PolySphereLP
