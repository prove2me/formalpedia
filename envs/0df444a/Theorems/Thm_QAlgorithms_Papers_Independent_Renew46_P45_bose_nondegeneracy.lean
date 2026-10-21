-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P45_bose_nondegeneracy
-- name    : QAlgorithms.Papers.Independent.Renew46.P45.bose_nondegeneracy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:42:20.599712+00:00
-- url     : https://prove2.me/theorems/9864e979-9b4f-4981-9dd0-07d569c6e99a
-- title:
--   Nondegeneracy of su(d) on the actual Bose representation
-- statement:
--   Let $d\ge2$ and $N\ge1$. Let $\pi_N^+$ be the restriction of $u\mapsto u^{\otimes N}$ to the actual Bose space $K=\operatorname{Sym}^N\mathbb C^d$. Let $\mathfrak{su}(d)$ be the real Lie algebra of traceless anti-Hermitian matrices. Every real-linear map $L:\mathfrak{su}(d)\to B(K)$ satisfying
--   $$
--   L(uXu^*)=\pi_N^+(u)L(X)\pi_N^+(u)^*\qquad(u\in SU(d),\ X\in\mathfrak{su}(d))
--   $$
--   has one common scalar $c\in\mathbb C$ such that
--   $$
--   L(X)=c\,\partial\pi_N^+(X)=c\left.\sum_{k=1}^N X_{(k)}\right|_K\qquad(X\in\mathfrak{su}(d)).
--   $$
--   This is operator-valued nondegeneracy, rather than proportionality assumed in advance.
--
--   **Formalization Note** The map is represented by an arbitrary real-linear extension to all matrices, with both hypotheses and conclusion tested only on $\mathfrak{su}(d)$. Finite-dimensional linear extension and restriction identify this formulation with the stated domain.
-- source:
--   Optimal Cloning of Pure States, Judging Single Clones, arXiv:quant-ph/9807010v1, PDF p. 4, Lemma 3; Appendix A4, p.13

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P45

noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Renew46.P45

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P45.unitaryMeasurable

/-- PDF p.4 Lemma 3 and p.13 Appendix A4: every real-linear equivariant
operator-valued map on su(d) is proportional to the actual Bose differential.
Maps are encoded by arbitrary real-linear extensions to all matrices, testing
only traceless anti-Hermitian inputs. Every map on su(d) extends in this way.
The printed vector-valued codomain in A4 is corrected to operators. -/
theorem bose_nondegeneracy (d N : ℕ) (hd : 2 ≤ d) (hN : 1 ≤ N)
    (L : Mat d →ₗ[ℝ] TensorMat d N)
    (hsupport : ∀ X : Mat d, Xᴴ = -X → Matrix.trace X = 0 →
      boseProjector d N * L X * boseProjector d N = L X)
    (hequiv : ∀ u : U d, Matrix.det (u : Mat d) = 1 →
      ∀ X : Mat d, Xᴴ = -X → Matrix.trace X = 0 →
      L ((u : Mat d) * X * (u : Mat d)ᴴ) =
        QAlgorithms.piKron N (u : Mat d) * L X * (QAlgorithms.piKron N (u : Mat d))ᴴ) :
    ∃ c : ℂ, ∀ X : Mat d, Xᴴ = -X → Matrix.trace X = 0 →
      L X = c • boseGenerator d N X := by sorry

end QAlgorithms.Papers.Independent.Renew46.P45

end
