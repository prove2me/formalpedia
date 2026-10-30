-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P07_asymptotic_fidelity_equivalence
-- name    : QAlgorithms.Papers.Independent.Advance50.P07.asymptotic_fidelity_equivalence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:41:45.615985+00:00
-- url     : https://prove2.me/theorems/603d01c3-41d1-4693-87a0-3215b6b86cc9
-- title:
--   Asymptotic equivalence of the fidelity criteria
-- statement:
--   Let $A,B$ be fixed nonzero finite-dimensional registers and let $\widehat\Phi=(\Phi_n)_{n\ge1}$ be arbitrary CPTP maps from $A^{\otimes n}$ to $B^{\otimes n}$. For each criterion $x\in\{\mathrm{ent},\min\}$, define $Q_x$ by unassisted subspace codes with positive integer ranks, arbitrary CPTP decoders, and the corresponding squared-overlap accuracy at least $1-\epsilon$. Both one-sided outer limits exist and
--
--   $$Q_{\rm ent}^\infty(\widehat\Phi)=Q_{\min}^\infty(\widehat\Phi),\qquad Q_x^\infty(\widehat\Phi)=\lim_{\epsilon\downarrow0}\liminf_{n\to\infty}\frac{Q_x(\Phi_n;\epsilon)}n.$$
--
--   The operational quantities are defined independently. This equivalence holds without a memoryless assumption.
-- source:
--   The quantum capacity of channels with arbitrarily correlated noise, arXiv:0902.0158v5, PDF p. 11, Equation (36), asymptotic equivalence of the two fidelity criteria

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

/-- Eq. (36), PDF p.11: arbitrary channel sequences, with separate
operational fidelity definitions and one-sided outer limits. -/
theorem asymptotic_fidelity_equivalence {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (Phi : (k : ℕ) → Superop (PositiveTensorBasis A k) (PositiveTensorBasis B k))
    (hPhi : ∀ k, IsChannel (Phi k)) :
    subspaceAsymptoticCapacity Phi false = subspaceAsymptoticCapacity Phi true ∧
    Tendsto (capacityRate Phi false) (𝓝[>] (0 : ℝ)) (𝓝 (subspaceAsymptoticCapacity Phi false)) ∧
    Tendsto (capacityRate Phi true) (𝓝[>] (0 : ℝ)) (𝓝 (subspaceAsymptoticCapacity Phi true)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P07

end
