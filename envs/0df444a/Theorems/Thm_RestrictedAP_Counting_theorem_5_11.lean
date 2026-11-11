-- Prove2me | Theorems.Thm_RestrictedAP_Counting_theorem_5_11
-- name    : RestrictedAP.Counting.theorem_5_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:19:16.932529+00:00
-- url     : https://prove2.me/theorems/6dd11e87-a58b-4a5d-8b25-d0b809966e2d
-- title:
--   Theorem 5.11 — multidimensional reverse hypercontractivity for jointly proper complex Gaussians
-- statement:
--   Let $\eta>0$, $\ell\in\mathbb N$, $n\ge1$, and let $G=(G_1,\dots,G_\ell)$ be a jointly proper ($\mathbb E[GG^{\mathsf T}]=0$) centred complex Gaussian collection of $\ell$ random vectors $G_j=(G_{j,1},\dots,G_{j,n})\in\mathbb C^n$ such that
--
--   1. each $G_j$ is distributed as $n$ independent standard complex Gaussians $\mathcal{CN}(0,1)$ (real and imaginary parts independent $N(0,1/2)$);
--   2. the $n\ell\times n\ell$ covariance matrix $P=\mathbb E[GG^*]$ satisfies $P-\eta I\succeq0$.
--
--   Then for all measurable $f_1,\dots,f_\ell:\mathbb C^n\to[0,1]$ with $\mathbb E[f_j(G_j)]=\mu_j$,
--   $$\mathbb E\Big[\prod_{j=1}^\ell f_j(G_j)\Big]\ \ge\ \Big(\prod_{j=1}^\ell\mu_j\Big)^{1/\eta}.$$
--
--   The paper derives it in Appendix A from the real-Gaussian theorem of [CDP15, HHM18]; in the proof of Theorem 1.4 it supplies the lower bound for the Gaussian counterpart of the 3-AP count.
--
--   **Formalization Note.** A jointly proper centred complex Gaussian vector with covariance $P$ is the law of $AZ$, $Z$ a vector of independent $\mathcal{CN}(0,1)$ variables (the published `BraneBrauer.Orthogonal.complexGaussian`) and $A$ any matrix with $AA^*=P$; the statement quantifies over $A$. Coordinates are indexed by $(j,k)\in$ `Fin ℓ × Fin n`.
--
--   Differences from the source:
--   - encoding: a jointly proper Gaussian collection G with covariance P = E[GG^*] → the law of A·Z with Z ∼ CN(0,1)^{⊗(ℓ×n)} and A A^* = P, quantified over A; reason: proper complex Gaussian laws are determined by their covariance, and A Z is jointly proper with covariance A A^*; same class of ensembles
--   - encoding: each G_i is n independent CN(0,1) Gaussians → (A A^*)_{(j,k),(j,k')} = [k = k']; reason: for a proper Gaussian vector, identity covariance of the block G_j is equivalent to independent CN(0,1) coordinates
--   - encoding: f_j ∈ L²(ℂ^n, γ_n) with values in [0, 1] → f_j measurable with 0 ≤ f_j ≤ 1 everywhere; reason: every L² class has a measurable representative, and changing f_j on a γ_n-null set changes no expectation
--   - reading: G_i = (G_{i,1}, …, G_{i,n}) with n unrestricted → n ≥ 1; reason: the vectors have coordinates; at n = 0 the hypothesis P − ηI ⪰ 0 holds for every η and the inequality fails for η > 1 (INSIGHTS I2)
-- source:
--   Bhangale, Khot, Liu, Minzer, A Counting Lemma for Somewhat Restricted 3-APs, arXiv:2608.17365 (copy sha256 de0b96c1…), p. 31, Theorem 5.11 (proof in Appendix A, pp. 53–56)

import Mathlib
import Definitions.Def_BraneBrauer_Orthogonal_ComplexGaussian

open MeasureTheory ComplexOrder

namespace RestrictedAP.Counting

/-- **Theorem 5.11** (p. 31), multidimensional reverse hypercontractivity for jointly proper
complex Gaussians. Let `η > 0` and let `G = (G_1, …, G_ℓ)` be a jointly proper complex Gaussian
ensemble of `ℓ` random vectors in `ℂ^n` such that each `G_i` is `n` independent `CN(0,1)`
Gaussians and the `nℓ × nℓ` covariance `P = E[G G^*]` satisfies `P − ηI ⪰ 0`. Then for all
measurable `f_1, …, f_ℓ : ℂ^n → [0,1]` with `E[f_j(G_j)] = μ_j`,
`E[∏_j f_j(G_j)] ≥ (∏_j μ_j)^{1/η}`.

Encoding: the coordinates of `G` are indexed by `(j, k) ∈ Fin ℓ × Fin n` (`G_{j,k}`). A jointly
proper (`E[G Gᵀ] = 0`) centred complex Gaussian vector with covariance `P` is exactly the law of
`A Z` with `Z` a vector of independent standard `CN(0,1)` variables
(`BraneBrauer.Orthogonal.complexGaussian`: real and imaginary parts independent `N(0, 1/2)`) and
`A` any matrix with `A A^* = P`; the statement quantifies over `A`. Condition 1 is
`(A A^*)_{(j,k),(j,k')} = [k = k']`, i.e. each block `E[G_j G_j^*]` is the identity. The vectors
`G_j` have `n ≥ 1` coordinates. -/
theorem theorem_5_11 (ℓ n : ℕ) (hn : 1 ≤ n) (η : ℝ) (hη : 0 < η)
    (A : Matrix (Fin ℓ × Fin n) (Fin ℓ × Fin n) ℂ)
    (hblock : ∀ (j : Fin ℓ) (k k' : Fin n),
      (A * A.conjTranspose) (j, k) (j, k') = if k = k' then 1 else 0)
    (hcov : (A * A.conjTranspose - (η : ℂ) • (1 : Matrix (Fin ℓ × Fin n) (Fin ℓ × Fin n) ℂ)).PosSemidef)
    (f : Fin ℓ → (Fin n → ℂ) → ℝ) (hf : ∀ j, Measurable (f j))
    (hf01 : ∀ j z, 0 ≤ f j z ∧ f j z ≤ 1) :
    let lawG : Measure (Fin ℓ × Fin n → ℂ) :=
      (Measure.pi (fun _ : Fin ℓ × Fin n => BraneBrauer.Orthogonal.complexGaussian)).map
        (fun z => A.mulVec z)
    (∏ j, ∫ g, f j (fun k => g (j, k)) ∂lawG) ^ (1 / η) ≤
      ∫ g, ∏ j, f j (fun k => g (j, k)) ∂lawG := by sorry

end RestrictedAP.Counting
