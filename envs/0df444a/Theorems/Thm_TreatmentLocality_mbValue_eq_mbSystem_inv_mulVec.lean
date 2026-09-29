-- Prove2me | Theorems.Thm_TreatmentLocality_mbValue_eq_mbSystem_inv_mulVec
-- name    : TreatmentLocality.mbValue_eq_mbSystem_inv_mulVec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T00:35:59.159463+00:00
-- url     : https://prove2.me/theorems/d3839226-44c9-4046-9451-07cd7ca1cc7c
-- title:
--   The plug-in value function solves $(\mathrm{Diag}(N)-\gamma K)\hat V = R$
-- statement:
--   **The plug-in value function solves a linear system with no divisions.** For an SST model with discount factor $\gamma$ and statistics $v$, write $N^a_i = \sum_k K^a_{ik}$ for the visit counts of arm $a$. If every visit count is nonzero, then the plug-in value function $\hat V^a = (I - \gamma \hat P^a)^{-1}\hat r^a$, built from the normalised estimates $\hat P^a_{ij} = K^a_{ij}/N^a_i$ and $\hat r^a_i = R^a_i/N^a_i$, is equally the solution of
--   $$\bigl(\mathrm{Diag}(N^a) - \gamma K^a\bigr)\, \hat V^a = R^a,$$
--   that is, $\hat V^a = (\mathrm{Diag}(N^a) - \gamma K^a)^{-1} R^a$.
--
--   The identity is the factorisation $\mathrm{Diag}(N^a) - \gamma K^a = \mathrm{Diag}(N^a)\,(I - \gamma \hat P^a)$ together with cancellation of $\mathrm{Diag}(N^a)$ against the normalisation of $\hat r^a$. Its point is that the right-hand side is built from the raw statistics by a **linear** map followed by a matrix inversion, while the left-hand side is not: this is the form in which the plug-in estimator is computed in practice, and the form in which it is differentiable by inspection.
-- source:
--   H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3: Section 2 (V = (I - γP)⁻¹ r), Remark 1 and Proposition 5 (the plug-in estimators P̂, r̂, V̂), Appendix EC.6 eq. (EC.4) (the visit-count weighted system), and Appendix EC.4.3, where the same derivatives ∂Δ/∂P(s,j) = γ(I - γP)⁻¹E_{s,j}V and ∂Δ/∂r are computed for the constrained Cramér-Rao bound of Theorem 5.

import Definitions.Def_TreatmentLocalityPlugIn

open MeasureTheory ProbabilityTheory TreatmentLocality
open scoped NNReal ENNReal

theorem TreatmentLocality.mbValue_eq_mbSystem_inv_mulVec {S : Type*} [DecidableEq S] [Fintype S]
    (M : Model S) (v : EstInput S) (a : Bool)
    (hN : ∀ i, ∑ k, (v a).1 i k ≠ 0) :
    mbValue M v a = (mbSystem M v a)⁻¹.mulVec (fun i => (v a).2 i) := by sorry
