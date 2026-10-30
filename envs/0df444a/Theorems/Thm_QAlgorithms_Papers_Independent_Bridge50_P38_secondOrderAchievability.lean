-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P38_secondOrderAchievability
-- name    : QAlgorithms.Papers.Independent.Bridge50.P38.secondOrderAchievability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:37:21.465286+00:00
-- url     : https://prove2.me/theorems/49e479ad-8669-4ac8-9599-c690b9949b91
-- title:
--   Second-order subspace-code achievability
-- statement:
--   All systems are nonempty finite-dimensional complex Hilbert spaces. The channel $\mathcal N:A\to B$ is completely positive and trace preserving, and its $n$ uses are independent. A code embeds a positive integer dimensional subspace of $A^{\otimes n}$ and uses a CPTP decoder into that ambient input space. Write $Q^{n,\varepsilon}$ for the supremum of $\log_2 m$ over codes with Haar-average squared pure-state fidelity at least $1-\varepsilon$, and $Q_{\rm et}^{n,\varepsilon}$ for the corresponding maximally entangled squared-overlap criterion. These are total qubits per block.
--
--   For a density input $\rho$, purify it as $\Psi^\rho_{RA}$ and put $\omega_{RB}=(\operatorname{id}_R\otimes\mathcal N)(\Psi^\rho)$. Let $I_c(\mathcal N)=\max_\rho D(\omega_{RB}\|I_R\otimes\omega_B)$, in bits, and let $S_c(\mathcal N)$ be all maximizing inputs. For $\varepsilon<1/2$, $V_\varepsilon$ is the minimum relative information variance over $S_c$; for $\varepsilon>1/2$ it is the maximum. Fix $0<\varepsilon<1$, and let $\Phi^{-1}$ be the standard normal quantile. There are $K>0$ and $n_0\ge2$, chosen before $n$, such that for $n\ge n_0$,
--
--   $$Q^{n,\varepsilon}(\mathcal N)\ge Q_{\rm et}^{n,\varepsilon}(\mathcal N)\ge nI_c(\mathcal N)+\sqrt{nV_\varepsilon(\mathcal N)}\,\Phi^{-1}(\varepsilon)-K\log_2 n.$$
--
--   The capacity comparison holds for every $n\ge1$. At $\varepsilon=1/2$ the second-order term is zero; no value is assigned to $V_{1/2}$. This is a one-sided achievability bound and makes no assertion of a Petz decoder witness.
-- source:
--   Decoding quantum information via the Petz recovery map, arXiv:1504.04449v4, PDF p. 18, Theorem 3.5 / (1.2),(3.19): second-order achievability

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P38

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Bridge50.P38

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

open QAlgorithms.Papers.Independent.Information100.P63 (normalQuantile)

open QAlgorithms.Papers.Independent.Dependency50.P36
  (relativeEntropyFinite pairInformationVariance)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (columnProjector pinch marginalAB marginalAC)

open QAlgorithms.Papers.Independent.Information100.P22
  (densityPurification singleUseInformation coherentInformation)

open QAlgorithms.Papers.Independent.Gap48.P23 (CompletelyPositive)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C : Type} [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

/-- PDF p.18, Theorem 3.5, (3.19), also p.2, (1.2): the claimed unrestricted
second-order capacity achievability.
Printed: Theorem 3.5 includes epsilon=1/2, but (2.5) defines V only off that value.
Changed: the whole second-order correction is zero at epsilon=1/2; V remains undefined there.
Why: the normal quantile at 1/2 is zero, and the fixed-input claim (3.25) gives this case
without assigning a dispersion value or imposing any further channel/input hypothesis.
This statement does not certify the source's proof or a Petz-decoder witness. -/
theorem secondOrderAchievability [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) (epsilon : ℝ)
    (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    (∀ n : ℕ, 1 ≤ n → subspaceCapacity true N n epsilon ≤ averageCapacity N n epsilon) ∧
    ∃ K : ℝ, 0 < K ∧ ∃ n0 : ℕ, 2 ≤ n0 ∧ ∀ n ≥ n0,
      (((n : ℝ) * singleUseInformation N + secondOrderCorrection N epsilon n -
        K * log2 n : ℝ) : EReal) ≤ subspaceCapacity true N n epsilon := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P38

end
