-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P91_graph_labels
-- name    : QAlgorithms.Papers.Independent.Intake100.P91.graph_labels
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:09:37.588381+00:00
-- url     : https://prove2.me/theorems/6000e915-6682-47dc-b875-e602d2790f5c
-- title:
--   Schur–Weyl–Young labels: Weyl endpoints and Young shape paths
-- statement:
--   Let $d\ge1$ and $n\ge0$ be integers. For a partition $\lambda$ of $n$ with at most $d$ rows, write $\mathsf W_d(\lambda)$ for its semistandard Weyl tableaux on $[d]$, $\mathsf Y(\lambda)$ for its standard Young tableaux, and $\mathsf P_d(\lambda)$ for the paths of one-box shape extensions from the empty diagram to $\lambda$. All modules below are complex. There is a bijection from $\mathsf Y(\lambda)$ to $\mathsf P_d(\lambda)$ sending a tableau to the shapes occupied by its first $i$ labels, for every $0\le i\le n$. Moreover,
--
--   $$
--   |\mathsf P_d(\lambda)|=\dim S^\lambda,\qquad
--   |\mathsf W_d(\lambda)|=\dim W^\lambda.
--   $$
--
--   Consequently the Schur labels $(\lambda,t,y)$ correspond bijectively to pairs consisting of the same Weyl endpoint $t$ and the shape path of $y$, and
--
--   $$
--   \left|\coprod_{\lambda\vdash n,\,\ell(\lambda)\le d}
--   \mathsf W_d(\lambda)\times\mathsf P_d(\lambda)\right|=d^n.
--   $$
--
--   Every such endpoint and shape path admits a compatible history of Weyl vertices whose adjacent GT patterns obey (16). Histories are not themselves counted as distinct basis labels. These assertions include the unique empty label and path at $n=0$.
--
--   This describes the simultaneous combinatorial labelling underlying the graph; it does not assert the deferred identification of recursively constructed physical vectors.
-- source:
--   A Multigraph Approach for Performing the Quantum Schur Transform, arXiv:2204.10694v1, PDF p. 8, §3, (13); §2.4 and §3.1.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P91

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P91

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- §3, PDF pp.8,11, with the basis-labelling consequence of §2.4, p.7.
Young tableaux correspond to shape paths; pairs with Weyl endpoints give all
d^n labels, including the vacuum. No bijection with individual vertex paths
is asserted. The dimensions refer to the constructed complex modules. -/
theorem graph_labels (d n : ℕ) (hd : 0 < d) :
    (∀ lambda : QAlgorithms.Schur.Partition d n,
      (∃ e : ShapedYoungTableau lambda ≃ ShapePath lambda, ∀ y, IsYoungPath y (e y)) ∧
      Nat.card (ShapePath lambda) = Module.finrank ℂ (QAlgorithms.Schur.spechtSpace lambda) ∧
      Nat.card (WeylTableau lambda) = Module.finrank ℂ (QAlgorithms.Schur.schurModule lambda)) ∧
    (∃ e : SchurLabels d n ≃ GraphLabels d n, ∀ a, LabelsCorrespond a (e a)) ∧
    Nat.card (GraphLabels d n) = d^n ∧
    (∀ label : GraphLabels d n, HasWeylLift label) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P91

end
