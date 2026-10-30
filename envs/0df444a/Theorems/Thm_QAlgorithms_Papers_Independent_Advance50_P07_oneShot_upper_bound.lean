-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P07_oneShot_upper_bound
-- name    : QAlgorithms.Papers.Independent.Advance50.P07.oneShot_upper_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:42:23.052085+00:00
-- url     : https://prove2.me/theorems/719c65e8-e2ff-4e92-96f9-65460f9cdaee
-- title:
--   One-shot entanglement-transmission upper bound
-- statement:
--   Let $\Phi:\mathcal B(A)\to\mathcal B(B)$ be CPTP on nonzero finite-dimensional input and output registers, and let $\epsilon\ge0$. For every nonzero input subspace $S$, form $\omega_S^{RB}$ from its normalized maximally entangled input as in (16)–(17). Using the effect-smoothed quantity (12), with normalized comparison states and $-\log_2(0)=+\infty$,
--
--   $$Q_{\rm ent}(\Phi;\epsilon)\le\max_{0\ne S\subseteq A}\widetilde I^c_{0,2\sqrt\epsilon}(\omega_S^{RB}).$$
--
--   The maximizing subspace, its effect and comparison-state optimizers, and an optimal operational transmission code exist. This upper bound is meaningful independently of the deferred lower half of Theorem 1.
-- source:
--   The quantum capacity of channels with arbitrarily correlated noise, arXiv:0902.0158v5, PDF p. 10, VII.B, unnumbered one-shot upper bound

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P07

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology

open Filter

namespace QAlgorithms.Papers.Independent.Advance50.P07

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P09 (relativeD petzD)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative Density elog)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P19 (marginalRA marginalRB)

open QAlgorithms.Papers.Independent.Support50.P21 (PositiveTensorBasis)

/-- VII.B, PDF p.10: independently meaningful upper half of Theorem 1.
An actual maximizing subspace is retained. Qent is finite even when
operator-smoothed coherent information has an infinite endpoint. -/
theorem oneShot_upper_bound {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (Phi : Superop A B) (hPhi : IsChannel Phi) (eps : ℝ) (heps : 0 ≤ eps) :
    ∃ S : Frame A,
      (∀ T : Frame A, operatorCoherent (frameOutput Phi T) (2 * Real.sqrt eps) ≤
        operatorCoherent (frameOutput Phi S) (2 * Real.sqrt eps)) ∧
      (qEnt Phi eps : EReal) ≤ operatorCoherent (frameOutput Phi S) (2 * Real.sqrt eps) ∧
      OperatorAttained (frameOutput Phi S) (2 * Real.sqrt eps) ∧
      EntRate Phi eps (qEnt Phi eps) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P07

end
