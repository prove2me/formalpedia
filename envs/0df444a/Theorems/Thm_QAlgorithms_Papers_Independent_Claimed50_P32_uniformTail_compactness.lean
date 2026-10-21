-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P32_uniformTail_compactness
-- name    : QAlgorithms.Papers.Independent.Claimed50.P32.uniformTail_compactness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:29:26.646449+00:00
-- url     : https://prove2.me/theorems/0742611b-9e72-4561-b458-60305a9fb4fb
-- title:
--   Uniform finite-rank tails characterize trace-norm compactness
-- statement:
--   Let $A$ be a trace-norm closed subset of the positive trace-class operators of trace at most one on a nonzero separable complex Hilbert space. Then
--
--   $$A\text{ is trace-norm compact}\quad\Longleftrightarrow\quad\forall\varepsilon>0\;\exists\text{ finite-rank orthogonal projection }P\;\forall X\in A,\quad\operatorname{Tr}((I-P)X)<\varepsilon.$$
--
--   The projector depends only on $\varepsilon$ and is uniform over $A$. Rank zero and the empty set are allowed. This is the Appendix's compactness criterion.
--
--   **Formalization Note** An orthonormal family $(v_a)_{a=1}^n$ represents $P$, and the tail equals $\operatorname{Tr}X-\sum_a\langle v_a,Xv_a\rangle$.
-- source:
--   On approximation of quantum channels, arXiv:0711.2245v1, PDF p. 24, §6, unnumbered Proposition: uniform-tail compactness criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P32

noncomputable section

open Filter

open scoped Topology ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Claimed50.P32

open QAlgorithms.RealRegisters (Hilbert)

/-- §6, Appendix Proposition, PDF p.24: a CLOSED subset of positive operators
of trace at most one is trace-norm compact iff a finite-rank projection captures
all but epsilon of every member's trace, uniformly over the set. -/
theorem uniformTail_compactness {I : Type} [Countable I] [Nonempty I] (A : Set (TraceSubstate I)) (hclosed : IsClosed A) :
    IsCompact A ↔ ∀ epsilon : ℝ, 0 < epsilon →
      ∃ (n : ℕ) (v : Fin n → Hilbert I), Orthonormal ℂ v ∧
        ∀ X ∈ A, traceTail X.val v < epsilon := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P32

end
