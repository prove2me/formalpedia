-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_sumRelationTraces
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.sumRelationTraces
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:19:27.107867+00:00
-- url     : https://prove2.me/theorems/2bc46eff-60f1-4287-8891-ec0683ef541d
-- title:
--   Sum of traces of relation tensors
-- statement:
--   Let $d$ be prime, $t\geq1$, and $n\geq0$. Each $R(T)$ has trace $|T\cap\Delta|^n$, where $\Delta$ is the diagonal relation. Their trace sum has the two product forms below. For $n=0$ this recovers the cardinality of $\Sigma_{t,t}(d)$, including the empty product at $t=1$.
--
--   $$
--   \sum_T\operatorname{tr}R(T)=d^n\prod_{k=0}^{t-2}(d^k+d^n)=d^{nt}\prod_{k=0}^{t-2}(1+d^{k-n}).
--   $$
--
--   This gives the source's sum of traces of relation tensors in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 45, remark-5.1

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF pp.45--46, Remark 5.1: individual traces and both finite-product forms, including n=0. -/
theorem sumRelationTraces (d n t : ℕ) [NeZero d] [Fact (Nat.Prime d)] (ht : 1 ≤ t) :
    (∀ T : Lagrangian d t, (tensorRelation n T.val).trace =
      ((Nat.card {x : ResidueRegister d t // (x, x) ∈ T.val} : ℂ) ^ n)) ∧
    (∑ T : Lagrangian d t, (tensorRelation n T.val).trace) = (momentNormalization d n t : ℂ) ∧
    (∑ T : Lagrangian d t, (tensorRelation n T.val).trace) =
      (d : ℂ) ^ (n * t) * ∏ k ∈ Finset.range (t - 1), (1 + (d : ℂ) ^ ((k : ℤ) - n)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
