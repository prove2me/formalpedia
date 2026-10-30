-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P08_minimal_exact_success_comparison
-- name    : QAlgorithms.Papers.Independent.Extend50.P08.minimal_exact_success_comparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:33:02.982464+00:00
-- url     : https://prove2.me/theorems/f289877c-cbda-4a3d-97e2-edd2f562ba9e
-- title:
--   Qubit success and failure comparison
-- statement:
--   For every $N\ge1$, let $p_m$ be success of the Bell-resource minimal SRM protocol and let $p_p$ be success of the canonical optimal exact qubit pPBT protocol constructed from (A5). Then
--
--   $$p_m=1-\frac{N+2}{2^{N+1}},\qquad p_p=1-\frac3{N+3},\qquad \frac{1-p_m}{1-p_p}=\frac{(N+2)(N+3)}{3\,2^{N+1}}\longrightarrow0.$$
--
--   For $N\ge2$, $p_p<p_m$; at $N=1$ they coincide. The exact failure ratio specifies the exponential success improvement being compared, without asserting any gate-count improvement, fidelity dominance or nonreducibility.
-- source:
--   Minimal Port-based Teleportation, arXiv:2111.05499v2, PDF p. 2, §I/§III A: qubit minimal-PBT success versus canonical optimal exact pPBT

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P08

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P08

attribute [local instance] Classical.propDecidable Classical.decEq

/-- §I, PDF p.2; Theorem 2 p.7, Fig.2 p.9, (A8) p.20: qubit success
comparison, with its exact exponentially small failure ratio. Equality occurs at N=1. -/
theorem minimal_exact_success_comparison :
    (∀ N : ℕ, 0 < N →
      pbtSuccess (1 : AliceMatrix 2 N) (minimalEffects 2 N) =
        1 - ((N : ℝ) + 2) / 2 ^ (N + 1) ∧
      pbtSuccess (probabilisticFilter 2 N) (probabilisticEffects 2 N) = 1 - 3 / ((N : ℝ) + 3) ∧
      (2 ≤ N → pbtSuccess (probabilisticFilter 2 N) (probabilisticEffects 2 N) <
        pbtSuccess (1 : AliceMatrix 2 N) (minimalEffects 2 N)) ∧
      (1 - pbtSuccess (1 : AliceMatrix 2 N) (minimalEffects 2 N)) /
        (1 - pbtSuccess (probabilisticFilter 2 N) (probabilisticEffects 2 N)) =
          (((N : ℝ) + 2) * (N + 3)) / (3 * 2 ^ (N + 1))) ∧
    Filter.Tendsto (fun N =>
      (1 - pbtSuccess (1 : AliceMatrix 2 N) (minimalEffects 2 N)) /
        (1 - pbtSuccess (probabilisticFilter 2 N) (probabilisticEffects 2 N)))
      Filter.atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P08

end
