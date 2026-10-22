-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P09_lemma1
-- name    : QAlgorithms.Papers.Independent.Gap20.P09.lemma1
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T23:20:00.767571+00:00
-- url     : https://prove2.me/theorems/b475debc-1a3c-444c-8290-209852bb4a38
-- title:
--   Lemma 1: permutation-independent conditional mutual information expansion
-- statement:
--   All registers below have finite, strictly positive dimension. States are positive semidefinite operators of trace one, channels are completely positive and trace preserving, and marginals are partial traces of the same state. Entropies use natural logarithms, with $0\log0=0$, and $\|\cdot\|_1$ denotes the full Schatten trace norm.
--
--   For a state $\rho$ on $A_1A'_1\cdots A_lA'_l$, with $l\ge1$, write
--   $$\Delta(\rho)=I(A_1A'_1:\cdots:A_lA'_l)_\rho-I(A'_1:\cdots:A'_l)_\rho,$$
--   where $I(C_1:\cdots:C_l)=\sum_i H(C_i)-H(C_1\cdots C_l)$.
--
--   For every permutation $\pi$ of $\{1,\ldots,l\}$,
--   $$\Delta(\rho)=\sum_{k=1}^l I\!\left(A_{\pi(k)};A_{\pi(1)}\cdots A_{\pi(k-1)}A'_{[l]\setminus\{\pi(k)\}}\mid A'_{\pi(k)}\right)_\rho.$$
--   Here $A'_{[l]\setminus\{i\}}$ consists of all primed systems except $A'_i$; the preceding unprimed collection is empty when $k=1$. Conditional mutual information is $I(X;Y\mid Z)=H(XZ)+H(YZ)-H(Z)-H(XYZ)$.
--
--   The identity expresses the same gap as a sum of conditional mutual informations in every ordering of the pairs.
-- source:
--   Multipartite quantum correlations and local recoverability, arXiv:1412.0333v3, PDF p. 5, Lemma 1: permutation-independent conditional mutual information expansion

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P09

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

open Filter

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

-- Exact accepted heterogeneous and selected-register bases; no local aliases.

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis)

open QAlgorithms.Papers.Independent.Gap48.P22
  (ReplicaBasis partyCopyMultiplicity selectedReplicaMarginal)

/-- PDF p.5, Lemma 1,(3.1): the full paired CMI expansion in EVERY order. -/
theorem lemma1 {l : ℕ} (hl : 0 < l) {D F : Fin l → Type}
    [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)]
    (rho : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ)
    (hrho : IsDensityMatrix rho) :
    ∀ order : Equiv.Perm (Fin l), informationGap rho = ∑ k, chainTerm rho order k := by sorry

end QAlgorithms.Papers.Independent.Gap20.P09

end
