-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P04_lemma11
-- name    : QAlgorithms.Papers.Independent.Gap20.P04.lemma11
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:50:38.765264+00:00
-- url     : https://prove2.me/theorems/38b9f07e-b9e5-4083-90c3-baef88467e18
-- title:
--   Lemma-11
-- statement:
--   Let $\mathcal N$ be a CPTP channel on nonzero finite-dimensional registers, with receiver and environment obtained by tracing the same Stinespring isometry. Optimize over all finite classical labels $X$, probability distributions, and normalized pure conditional states on a finite reference $A$ and input $A'$. For the resulting state, write $\chi=I(X;B)$, $q=I(A\rangle BX)$, $a=H(A|X)$, and $j=I(AX;B)$, with entropy in bits. Rates are nonnegative, and $E$ denotes consumed ebits. The capacity regions are the closures of positive-blocklength scaled unions in Section III; their one-use unions have no added closure.
--
--   Choose one point $s_{CQ}(\lambda)$ on each supporting face maximizing $C+\lambda Q$, $\lambda\ge1$, of the full CQ region, and one point $s_{CE}(\lambda)$ maximizing $C-\lambda E$, $0\le\lambda\le1$, of the full CE region. Include the resource endpoints and limits. Then
--   $$\mathcal C_{CQ}(\mathcal N)=\overline{\operatorname{co}}\,\mathsf M_{CQ}
--   \bigl(\{s_{CQ}(\lambda):\lambda\ge1\}\cup\text{axis endpoints}\bigr),$$
--   $$\mathcal C_{CE}(\mathcal N)=\overline{\operatorname{co}}\,\mathsf M_{CE}
--   \bigl(\{s_{CE}(\lambda):0\le\lambda\le1\}\cup\text{zero-consumption endpoint}\bigr).$$
--   Here $\mathsf M_{CQ}$ allows lowering both nonnegative rates; $\mathsf M_{CE}$ allows lowering $C$ and increasing consumption $E$. A single selection can omit points on constant-slope faces, which are recovered by convex combinations; no unique or smooth parametrization is asserted.
-- source:
--   Trade-off capacities of the quantum Hadamard channels, arXiv:1001.1732v2, PDF p. 21, Lemma-11

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P04

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P04

open QAlgorithms

open QAlgorithms.Papers.Independent.Claimed50.P24
  (Dilation PhysicalDilation ChannelEB Hadamard EqualMax AdditiveMax
   dephasingDilation dephasingGamma cloningDilation)

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel dilationPower)

open QAlgorithms.Papers.Independent.Information100.P32 (diagonal)

open QAlgorithms.Papers.Independent.Dependency50.P24 (ensembleHolevoBits)

open QAlgorithms.Papers.Independent.Gap48.P44 (cqTimeSharing ceTimeSharing)

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I B E J D F : Type}

variable [Fintype I] [Fintype B] [Fintype E]

variable [Fintype J] [Fintype D] [Fintype F]

variable [DecidableEq I] [DecidableEq B] [DecidableEq E]

variable [DecidableEq J] [DecidableEq D] [DecidableEq F]

variable [Nonempty I] [Nonempty B] [Nonempty E]

variable [Nonempty J] [Nonempty D] [Nonempty F]

/-- PDF pp.11,21, Lemma 11: one support optimizer per weight recovers the entire
resource region by convex combinations and endpoint limits. On the boundary,
nonselected points recovered by nontrivial combinations lie on constant-slope faces.
The selection hypotheses refer to full regularized regions, not one-use objectives
for an arbitrary channel, and make no uniqueness or differentiability assertion. -/
theorem lemma11 (U : Dilation I B E) (hU : PhysicalDilation U)
    (cqSelect ceSelect : ℝ → ℝ × ℝ)
    (hCQ : ∀ lam : ℝ, 1 ≤ lam → CQSupport (capacityCQ U) lam (cqSelect lam))
    (hCE : ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      CESupport (capacityCE U) lam (ceSelect lam)) :
    capacityCQ U = selectedCQHull (capacityCQ U) cqSelect ∧
      capacityCE U = selectedCEHull (capacityCE U) ceSelect := by sorry

end QAlgorithms.Papers.Independent.Gap20.P04

end
