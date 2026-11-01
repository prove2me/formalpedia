-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P70_arbitrarilyManyUses
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P70.arbitrarilyManyUses
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:39:50.840985+00:00
-- url     : https://prove2.me/theorems/65e22ad3-1c5d-4619-bdc2-a248ca6d6ebc
-- title:
--   Arbitrarily many uses can fail to detect positive quantum capacity
-- statement:
--   Let $n\geq1$ be an integer. For a finite-dimensional quantum channel $\mathcal C$, write
--   $$
--   Q^{(t)}(\mathcal C)=\frac1t\max_{\rho} I_{\mathrm{coh}}(\mathcal C^{\otimes t},\rho),\qquad
--   Q(\mathcal C)=\sup_{t\geq1}Q^{(t)}(\mathcal C),
--   $$
--   where the maximization ranges over all positive semidefinite, trace-one joint input matrices, including entangled inputs. Entropies and rates are in bits, and $Q$ is the unassisted quantum capacity.
--
--   There exist positive finite-dimensional input and output registers, a completely positive trace-preserving channel $\mathcal C$ between them, and an integer $t>n$ such that
--   $$
--   Q^{(n)}(\mathcal C)=0,\qquad Q^{(t)}(\mathcal C)>0,\qquad Q(\mathcal C)>0.
--   $$
--   The register dimensions may depend on $n$. This shows that no fixed finite number of channel uses suffices to detect positive quantum capacity for every channel.
-- source:
--   Unbounded number of channel uses are required to see quantum capacity, arXiv:1408.5115v1, PDF p. 1, Abstract/introduction; proved by Supplementary Theorem, p.11

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P70

namespace QAlgorithms.Papers.Independent.Intakenext100.P70

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22
  (Op coherentInformation singleUseInformation quantumCapacity mixed)

/-- Abstract/introduction, PDF pp.1--2; proved on p.11: no finite block length detects
positive capacity for every channel. Dimensions may grow with n; all inputs are optimized. -/
theorem arbitrarilyManyUses (n : ℕ) (hn : 0 < n) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ∃ Phi : Superop (Fin a) (Fin b),
      IsChannel Phi ∧ cubittBlockInformation Phi n = 0 ∧
      ∃ t : ℕ, n < t ∧ 0 < cubittBlockInformation Phi t ∧ 0 < quantumCapacity Phi := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P70
