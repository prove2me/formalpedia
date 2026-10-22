-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P09_proposition3
-- name    : QAlgorithms.Papers.Independent.Gap20.P09.proposition3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:22:26.103772+00:00
-- url     : https://prove2.me/theorems/487c0467-620a-4390-b4f7-7fd3a14e5466
-- title:
--   Proposition 3: approximate faithfulness of MSQ discord, both directions
-- statement:
--   All registers below have finite, strictly positive dimension. States are positive semidefinite operators of trace one, channels are completely positive and trace preserving, and marginals are partial traces of the same state. Entropies use natural logarithms, with $0\log0=0$, and $\|\cdot\|_1$ denotes the full Schatten trace norm.
--
--   Let $\rho$ be a state on $A_1\cdots A_l$, $l\ge1$. Define its multipartite symmetric quantum discord by
--   $$D(\rho)=I(A_1:\cdots:A_l)_\rho-\sup_{\mathcal M_1,\ldots,\mathcal M_l}I(X_1:\cdots:X_l)_{(\otimes_i\mathcal M_i)(\rho)},$$
--   where each $\mathcal M_i$ is a finite-outcome POVM measurement, with unrestricted outcome dimension. Let $h_2(t)=-t\log t-(1-t)\log(1-t)$, with its continuous endpoint values.
--
--   Both of the following hold:
--
--   1. For every $\varepsilon\in[0,1]$, if there are local entanglement-breaking channels $\mathcal E_i:A_i\to A_i$ with $\|\rho-(\otimes_i\mathcal E_i)(\rho)\|_1\le\varepsilon$, then
--   $$D(\rho)\le(l+1)h_2(\varepsilon/2)+\varepsilon\sum_{i=1}^l\log\dim A_i.$$
--   2. For every $\varepsilon>0$, if $D(\rho)\le\varepsilon$, there exist such channels with
--   $$\|\rho-(\otimes_i\mathcal E_i)(\rho)\|_1\le2l\sqrt\varepsilon.$$
--
--   This characterizes small MSQ discord quantitatively through approximate local entanglement-breaking fixed points. No optimal POVM is assumed to exist.
-- source:
--   Multipartite quantum correlations and local recoverability, arXiv:1412.0333v3, PDF p. 7, Proposition 3: approximate faithfulness of MSQ discord, both directions

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

/-- PDF p.7, Proposition 3,(4.4)–(4.7): both quantitative directions;
epsilon=0 is included only in the first direction. -/
theorem proposition3 {l : ℕ} (hl : 0 < l) {D : Fin l → Type}
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hrho : IsDensityMatrix rho) :
    (∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
      (∃ E : (i : Fin l) → Superop (D i) (D i),
        (∀ i, IsEBChannel (E i)) ∧ traceNorm (rho - multipartiteTensorAction E rho) ≤ eps) →
      msqDiscord rho ≤ ((l : ℝ) + 1) * Real.binEntropy (eps / 2) +
        eps * ∑ i, Real.log (Fintype.card (D i))) ∧
    (∀ eps : ℝ, 0 < eps → msqDiscord rho ≤ eps →
      ∃ E : (i : Fin l) → Superop (D i) (D i),
        (∀ i, IsEBChannel (E i)) ∧
        traceNorm (rho - multipartiteTensorAction E rho) ≤ 2 * (l : ℝ) * Real.sqrt eps) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P09

end
