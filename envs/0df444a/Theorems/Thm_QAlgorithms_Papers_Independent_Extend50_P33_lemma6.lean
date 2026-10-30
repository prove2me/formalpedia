-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P33_lemma6
-- name    : QAlgorithms.Papers.Independent.Extend50.P33.lemma6
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:51:24.586842+00:00
-- url     : https://prove2.me/theorems/8b8d1eba-c7aa-48c0-bdc5-e23037eab941
-- title:
--   Lemma 6: fixed-resource dual witness
-- statement:
--   Let $d\ge2$ be the local dimension, $N\ge2$ the number of ports, and $n=N+1$. All physical diagrams have height at most $d$. Write $m_\lambda$ for its multiplicity in the natural tensor permutation action, $d_\lambda$ for its Specht dimension, and $P_\lambda$ for the full isotypic projector. The relation $\mu\in\alpha$ means adding one box. A maximizing successor selector $\mu_*(\alpha)$ exists for every $\alpha$. For every such selector, the explicit matrix $\Omega=\sum_\alpha d\,m_\alpha F_{\mu_*(\alpha)}(\alpha)/m_{\mu_*(\alpha)}$ is dual feasible, with
--
--   $$\frac{\operatorname{Tr}\Omega}{d^{N+1}}=\frac1{d^N}\sum_\alpha m_\alpha^2\frac{d_{\mu_*(\alpha)}}{m_{\mu_*(\alpha)}}.$$
--
--   Every fixed-resource attainable success probability is bounded above by this value. This uses the correct multiplicity-ratio expression of Eq.(107), avoiding its incorrect final gamma rewrite.
-- source:
--   Port-based teleportation in arbitrary dimension, arXiv:1612.09260v3, PDF p. 12, Lemma 6: fixed-resource dual witness

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P33

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted type constructors; local notation only reorders Word's arguments.

local notation "Word" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P58.Word r d)

local notation "Op" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P21.Op
    (QAlgorithms.Papers.Independent.Information100.P58.Word r d))

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

/-- PDF pp.12,28 Lemma6: the explicit dual witness and multiplicity-ratio
objective, avoiding the missing-N final rewrite in Eq.(107). -/
theorem lemma6 (d k : ℕ) (hd : 2 ≤ d) :
    (∃ s : Schur.Partition d (k+1) → Schur.Partition d (k+2), MaxSelector s) ∧
    (∀ s : Schur.Partition d (k+1) → Schur.Partition d (k+2), MaxSelector s →
      FixedDual (fixedOmega s) ∧
      (fixedOmega s).trace.re / (d:ℝ)^(k+3) =
        (1/(d:ℝ)^(k+2)) * (∑ a, (mult a:ℝ)^2 * (sdim (s a):ℝ) / mult (s a)) ∧
      ∀ p ∈ fixedValues d k, p ≤ (fixedOmega s).trace.re / (d:ℝ)^(k+3)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P33

end
