-- Prove2me | Theorems.Thm_QVolKLS_Supplement_theorem_5_2
-- name    : QVolKLS.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:35:41.623969+00:00
-- url     : https://prove2.me/theorems/11b9bc52-eeb4-4fb6-b586-a3b24b3d621d
-- title:
--   Theorem 5.2 — one finite walk for each covariance branch
-- statement:
--   Fix the convex body, its rational inner and outer ball data, a finite rational list of tilts, rational spectral bounds $0<\lambda_-\le\lambda_+$, a certified $0<\psi\le\psi_D$, and accuracies $\eta,\zeta,\varepsilon_{\mathrm{Cov}}\in(0,1/2)$. There are common dyadic lattice, radius, seed, and arithmetic-precision parameters that work for every listed tilt and every rational symmetric $A$ with $\lambda_-I\preceq A\preceq\lambda_+I$. For each such branch:
--
--   1. Algorithm 2 is lazy, positive, irreducible, and reversible for the lattice log-affine law.
--   2. If $A$ is covariance-comparable with a fixed comparison constant, its two-warm mixing time is $\widetilde O(D^2/\psi^2)$.
--   3. Its zero-extended discriminant has an arbitrarily accurate implementation of an exact $1$-block-encoding using $O(1)$ coherent membership queries.
--   4. Every listed lattice normalizer has relative error at most $\zeta$.
--   5. With $L=\lceil C_{\mathrm{sample}}D(1+\log(4/\varepsilon_{\mathrm{Cov}}))^2\rceil$ independent lattice samples, the empirical covariance $\widehat\Sigma_i$ satisfies
--      $$
--      \Pr[\tfrac14\Sigma_i\preceq\widehat\Sigma_i\preceq4\Sigma_i]\ge1-\varepsilon_{\mathrm{Cov}}.
--      $$
--
--   Moreover, after normalizing the inner radius, the inverse mesh is bounded by one absolute polynomial in all displayed geometric, tilt, spectral, accuracy, failure-budget, and KLS parameters.
--
--   **Formalization Note** The soft-$O$ and polynomial claims are expanded as $C(D^2/\psi^2)(1+\log\Xi)^C$ and $2^p\le C\Xi^C$, with constants fixed before the varying data and with $\Xi$ listing every required parameter and reciprocal. The empirical covariance is expressed by all directional quadratic forms.
--
--   Differences from the source:
--   - encoding: the source describes Algorithm 2 operationally and states matrix inequalities → Lean packages the common finite proposal, Metropolis kernel, dyadic probabilities, block encoding, and covariance inequalities as explicit predicates on the same finite lattice; reason: a direct finite-state encoding of the same algorithm and Loewner-order clauses
--   - encoding: the source writes $\widetilde O(D^2/\psi^2)$ and “at most polynomial” → Lean uses $C(D^2/\psi^2)(1+\log\Xi)^C$ and $2^p\le C\Xi^C$ with one displayed aggregate $\Xi$; reason: makes every hidden absolute constant and parameter dependence explicit
--   - generalization: the source leaves the finite direction-sampler accuracy implicit in the common precision choice → Lean additionally chooses each walk with nonnegative direction error at most $1/100$; reason: Appendix B's construction permits arbitrary sufficiently fine precision, and the source's walks specialize to this choice
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), Theorem 5.2, p.40; Algorithm 2, pp.38-39; Appendix B.6, pp.77-78, especially (103)

import Definitions.Def_QVolKLS_Supplement_LatticeWalk

set_option autoImplicit false

namespace QVolKLS.Supplement

open MeasureTheory
open scoped ENNReal

/-- R. Zhang, arXiv:2610.04987 (held version, sha256 eee7a45e…), **Theorem 5.2
(One finite walk for each covariance branch)**, p.40, in the setting of §5.1, pp.37–40 and
Appendix B.6, pp.77–78.

One dyadic mesh and one radius/seed/precision regime work simultaneously for the whole finite tilt
list and every rational preconditioner in the supplied spectral range. Every resulting Algorithm 2
walk is lazy, positive, irreducible and reversible for the lattice law. A covariance-comparable
preconditioner has the stated uniform two-warm mixing bound; every walk has an arbitrarily accurate
zero-extended discriminant block-encoding with a constant number of coherent membership queries;
all normalizers and empirical covariances have the printed accuracy guarantees; and the inverse
mesh is polynomially bounded in every listed parameter.

The finite walk is tied to the paper's actual construction: its local finite-seed law approximates
the rounded uniform-ball proposal (83), its radius list is (85), and its connector is the uniform
signed integer-box proposal. The register covers every lattice point of the body and the connector
box covers every feasible difference.

**Formalization Note.** The universal comparison constant `c` is fixed before all dimensions and
inputs. `Õ(D²/ψ²)` is expanded as `C (D²/ψ²) (1+log Xi)^C`, and the final polynomial mesh
claim as `2^p ≤ C Xi^C`, with the same absolute `C` fixed before the data. `Xi` includes every
geometric bound and reciprocal, the largest tilt norm, both regularization bounds and reciprocals,
all three accuracy/failure reciprocals, `1/ψ`, the dimension and the number of stages. The sample
count is exactly the natural ceiling of `Csample D(1+log(4/εCov))²` for a universal sufficiently
large `Csample`. The statement fixes the body before choosing the common parameters, as printed.
-/
theorem theorem_5_2 :
    ∀ c : ℝ, 1 ≤ c →
      ∃ (C Csample Cq : ℝ), 0 < C ∧ 0 < Csample ∧ 0 < Cq ∧
        ∀ (D m : ℕ), 1 ≤ D →
        ∀ (K : Set (Euc D)) (xc : Fin D → ℚ) (r0 R0 : ℚ)
          (bt : Fin (m + 1) → Fin D → ℚ) (lm lp psi eta zeta epsCov : ℚ),
          IsConvexBody K → Metric.ball (ratPoint xc) (r0 : ℝ) ⊆ K →
          K ⊆ Metric.closedBall (ratPoint xc) (R0 : ℝ) →
          0 < r0 → r0 ≤ R0 → 0 < lm → lm ≤ lp → 0 < psi →
          ENNReal.ofReal (psi : ℝ) ≤ (SongZhangKLS.psiN D)⁻¹ →
          0 < eta → eta < 1 / 2 → 0 < zeta → zeta < 1 / 2 →
          0 < epsCov → epsCov < 1 / 2 →
          let Bstar : ℝ := ⨆ i, ‖ratPoint (bt i)‖
          let Xi : ℝ := 1 + (D : ℝ) + (m : ℝ) + (r0 : ℝ) + (R0 : ℝ) +
            1 / (r0 : ℝ) + 1 / (R0 : ℝ) + Bstar + (lm : ℝ) + (lp : ℝ) +
            1 / (lm : ℝ) + 1 / (lp : ℝ) + 1 / (eta : ℝ) + 1 / (zeta : ℝ) +
            1 / (epsCov : ℝ) + 1 / (psi : ℝ)
          let L : ℕ := ⌈Csample * (D : ℝ) * (1 + Real.log (4 / (epsCov : ℝ))) ^ 2⌉₊
          ∃ q : CommonWalkParams D,
            RegCovers D q.b q.p (Metric.closedBall (ratPoint xc) (R0 : ℝ)) ∧
            ConnectorCovers q (R0 : ℝ) ∧
            (2 : ℝ) ^ q.p ≤ C * Xi ^ C ∧
            (∀ (i : Fin (m + 1)) (A : Matrix (Fin D) (Fin D) ℚ), A.transpose = A →
              (∀ u : Euc D,
                (lm : ℝ) * ‖u‖ ^ 2 ≤ quadForm A u ∧ quadForm A u ≤ (lp : ℝ) * ‖u‖ ^ 2) →
              ∃ W : LatticeWalk q K (ratPoint (bt i)) A,
                0 ≤ W.epsDir ∧ W.epsDir ≤ 1 / 100 ∧
                TransformedOuterRadiusBound q K (ratPoint xc) W.WA ∧
                (∃ rhoA : ℝ, TransformedCellRadiusBound q W.WA rhoA ∧
                  q.rMesh = C * (D : ℝ) ^ 3 * rhoA) ∧
                HasConstantQueryBlockEncoding q K (ratPoint (bt i)) A W Cq ∧
                ((∀ u : Euc D,
                    c⁻¹ * dirVariance (logAffineMeasure K (ratPoint (bt i))) u ≤ quadForm A u ∧
                    quadForm A u ≤ c * dirVariance (logAffineMeasure K (ratPoint (bt i))) u) →
                  ∃ t : ℕ,
                    (t : ℝ) ≤ C * ((D : ℝ) ^ 2 / (psi : ℝ) ^ 2) *
                      (1 + Real.log Xi) ^ C ∧
                    MixTime2Le (walkOmega q K) eta (walkLaw q K (ratPoint (bt i))) W.P t)) ∧
            (∀ i : Fin (m + 1),
              |latticeZ K ((2 : ℝ)⁻¹ ^ q.p) (ratPoint (bt i)) /
                  logAffineZ K (ratPoint (bt i)) - 1| ≤ zeta ∧
              1 - (epsCov : ℝ) ≤
                covarianceGoodProbability (L := L) q K (ratPoint (bt i))) := by sorry

end QVolKLS.Supplement
