-- Prove2me | Theorems.Thm_RestrictedAP_Counting_gaussian_covariance_model
-- name    : RestrictedAP.Counting.gaussian_covariance_model
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:59:52.880541+00:00
-- url     : https://prove2.me/theorems/31f84540-fee2-4037-bda8-8aedec5eda18
-- title:
--   Proper Gaussian covariance model with the uniform covariance gap
-- statement:
--   Given an orthonormal nonconstant Fourier basis for the common marginal $\nu$, construct three jointly proper Gaussian vectors indexed by coordinate and nonconstant basis element. Their diagonal blocks are standard Gaussian and, on used coordinates,
--   $$\operatorname{Cov}(G_{i,t,j},G_{i',t,j'})=\mathbb E_{(x,y,z)\sim\mu}[\varphi_j(x_{(i)})\overline{\varphi_{j'}(x_{(i')}})],$$
--   while different coordinates are independent. The covariance is represented as $AA^*$, with $AA^*-\eta I\succeq0$ uniformly in alphabets of size at most $m$ and atom bound $s$. An additional dummy Gaussian coordinate is included so the formal statement also covers $n=0$ and $q'=0$.
-- source:
--   Bhangale–Khot–Liu–Minzer, arXiv:2608.17365 (paper #1020), §5.1.3 pp.32–33, especially the construction of $\mathcal G_{\vec b,\vec b^\star}$ and its covariance formula, together with Proposition 5.28 pp.36–37 for the uniform positive-definiteness gap; Definition 2.22 pp.13–14 supplies the covariance square-root representation $L=AA^*$. The dummy-coordinate convention handles $n=0$ without changing any used covariance.

import Mathlib
import Definitions.Def_RestrictedAP_Counting_GaussianInterface
import Theorems.Thm_RestrictedAP_Counting_proposition_5_28_uniform

namespace RestrictedAP.Counting

open MeasureTheory ComplexOrder

/-- Construction of the proper Gaussian covariance model in §5.1.3, with the uniform
positive-definiteness gap from Proposition 5.28. One independent dummy coordinate is added
so that the block dimension is positive even when `n = 0` or `q' = 0`. -/
theorem gaussian_covariance_model (m : ℕ) (s η : ℝ) (hs : 0 < s) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig] [Nonempty Sig], Fintype.card Sig ≤ m →
    ∀ (μ : Sig × Sig × Sig → ℝ) (ν : Sig → ℝ), IsDist μ →
      (∀ i : Fin 3, marginal μ i = ν) → (∀ x : Sig, μ (x, x, x) ≠ 0) →
      ¬ DistHasEmbedding ℤ μ → AtomsAtLeast μ s →
    ∀ (n q' : ℕ), Fintype.card Sig = q' + 1 →
    ∀ φ : Fin (q' + 1) → Sig → ℂ,
      (∀ a, φ 0 a = 1) →
      (∀ j k, ∑ a, (ν a : ℂ) * star (φ j a) * φ k a = if j = k then 1 else 0) →
    ∃ A : Matrix (Fin 3 × Fin (n * q' + 1)) (Fin 3 × Fin (n * q' + 1)) ℂ,
      (∀ (j : Fin 3) (k k' : Fin (n * q' + 1)),
        (A * A.conjTranspose) (j, k) (j, k') = if k = k' then 1 else 0) ∧
      (A * A.conjTranspose - (η : ℂ) •
        (1 : Matrix (Fin 3 × Fin (n * q' + 1)) (Fin 3 × Fin (n * q' + 1)) ℂ)).PosSemidef ∧
      (∀ (i j : Fin 3) (k l : Fin n × Fin q'),
        (A * A.conjTranspose) (i, baseCoord k) (j, baseCoord l) =
          if k.1 = l.1 then
            ∑ t, (μ t : ℂ) * φ k.2.succ (coord3 i t) * star (φ l.2.succ (coord3 j t))
          else 0) := by sorry
