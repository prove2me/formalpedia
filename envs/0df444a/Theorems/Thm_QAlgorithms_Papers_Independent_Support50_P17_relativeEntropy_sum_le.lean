-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P17_relativeEntropy_sum_le
-- name    : QAlgorithms.Papers.Independent.Support50.P17.relativeEntropy_sum_le
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-29T18:22:17.180734+00:00
-- url     : https://prove2.me/theorems/34f63154-152a-48d8-8884-65c5056b310f
-- title:
--   Joint subadditivity of the (unnormalised) Umegaki relative entropy
-- statement:
--   Let $\mathcal H$ be a finite-dimensional complex Hilbert space and let $(A_i)_{i\in s}$, $(B_i)_{i\in s}$ be finite families of positive semidefinite operators on $\mathcal H$ (not necessarily of trace one) such that $\ker B_i\subseteq\ker A_i$ for every $i$. With the Umegaki relative entropy $D(A\|B)=\operatorname{Tr}A\log A-\operatorname{Tr}A\log B$ (with $0\log 0=0$, and $+\infty$ when $\ker B\not\subseteq\ker A$),
--
--   $$
--   D\Big(\sum_{i\in s}A_i\,\Big\|\,\sum_{i\in s}B_i\Big)\le\sum_{i\in s}D(A_i\|B_i).
--   $$
--
--   This is the joint convexity of the quantum relative entropy (Lindblad 1974, a consequence of Lieb's concavity theorem) combined with its positive homogeneity $D(\lambda A\|\lambda B)=\lambda D(A\|B)$. It is the basic tool for splitting a pair of operators into simpler pieces.
--
--   **Formalization Note** The relative entropy is the frozen `relativeEntropy` of Dependency50.P21, valued in `EReal`; the sum on the right is taken in `EReal`.
-- source:
--   Lindblad, Expectations and entropy inequalities for finite quantum systems, Commun. Math. Phys. 39 (1974) 111-119, Theorem 3 (joint convexity) with homogeneity; used in Audenaert--Eisert, Continuity bounds on the quantum relative entropy - II, arXiv:1105.2656v3, proof of Corollary 1 (PDF p. 9), splitting step

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P17

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

namespace QAlgorithms.Papers.Independent.Support50.P17

attribute [local instance] Classical.propDecidable Classical.decEq

theorem relativeEntropy_sum_le {I ι : Type*} [Fintype I] [DecidableEq I] (s : Finset ι)
    (A B : ι → Matrix I I ℂ) (hA : ∀ i ∈ s, (A i).PosSemidef) (hB : ∀ i ∈ s, (B i).PosSemidef)
    (hAB : ∀ i ∈ s, IsSupported (A i) (B i)) :
    relativeEntropy (∑ i ∈ s, A i) (∑ i ∈ s, B i) ≤ ∑ i ∈ s, relativeEntropy (A i) (B i) := by sorry

end QAlgorithms.Papers.Independent.Support50.P17

end
