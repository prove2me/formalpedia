-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P07_memoryless_capacity
-- name    : QAlgorithms.Papers.Independent.Advance50.P07.memoryless_capacity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:32:21.53423+00:00
-- url     : https://prove2.me/theorems/d35dc670-0b2b-4815-b45b-31bb27f4f37c
-- title:
--   Memoryless capacity as a regularized subspace coherent information
-- statement:
--   Let $\Phi:\mathcal B(A)\to\mathcal B(B)$ be a CPTP map between nonzero finite-dimensional registers. For a nonzero subspace $S\subseteq A^{\otimes n}$ let $\omega_S^{RB}$ be the output marginal obtained from its rank-$\dim S$ maximally entangled input, with a full reference copy of $A^{\otimes n}$. Write $I^c(\omega)=S(\omega^B)-S(\omega^{RB})$, where entropy uses base-two logarithms. The finite-block maxima are attained, the ordinary limit below exists as a finite real number, and
--
--   $$Q_{\rm ent}^\infty(\Phi)=\lim_{n\to\infty}\frac1n\max_{0\ne S\subseteq A^{\otimes n}}I^c(\omega_S^{RB}).$$
--
--   The capacity on the left uses the separate operational entanglement-transmission definition and its one-sided vanishing-error limit. This is the paper's subspace-input form of the memoryless quantum capacity theorem.
-- source:
--   The quantum capacity of channels with arbitrarily correlated noise, arXiv:0902.0158v5, PDF p. 11, Theorem 2 (memoryless channels)

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

/-- Theorem 2, PDF pp.11–13, (37). Ordinary limit and finite-block
maximizers are conclusions. Input optimization is over subspaces. -/
theorem memoryless_capacity {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (Phi : Superop A B) (hPhi : IsChannel Phi) :
    (∀ k : ℕ, ∃ S : Frame (PositiveTensorBasis A k),
      stateCoherentBits (frameOutput (memoryless Phi k) S) = bestCoherent (memoryless Phi k)) ∧
    ∃ q : ℝ, subspaceAsymptoticCapacity (memoryless Phi) false = (q : EReal) ∧
      Tendsto (fun k : ℕ => bestCoherent (memoryless Phi k) / (k+1 : ℕ)) atTop (𝓝 q) ∧
      Tendsto (capacityRate (memoryless Phi) false) (𝓝[>] (0 : ℝ)) (𝓝 (q : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P07

end
