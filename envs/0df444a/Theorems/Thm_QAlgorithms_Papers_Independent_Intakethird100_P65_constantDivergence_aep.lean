-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P65_constantDivergence_aep
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P65.constantDivergence_aep
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:53:56.131647+00:00
-- url     : https://prove2.me/theorems/5400b0b0-d7f9-405b-8bca-51b5b7c19ce4
-- title:
--   Eq.(68): constant-channel divergence form of the AEP
-- statement:
--   All systems have finite positive dimension and fixed computational bases. Matrix order is Loewner order and logarithms are base two.
--
--   Let $\mathcal N:A'\to B$ be CPTP and let $\mathcal G_n$ be all replacement channels from $A'^{n}$ to $B^n$, allowing arbitrary correlated output densities. Define $D(\mathcal N\|\mathcal M)$ as the supremum of output-state relative entropy over purified input densities, with support failure giving $+\infty$. Then
--
--   $$\lim_{\varepsilon\downarrow0}\lim_{n\to\infty}\frac1n\inf_{\mathcal M_n\in\mathcal G_n}D_{\max}^{\varepsilon}(\mathcal N^{\otimes n}\|\mathcal M_n)=\inf_{\mathcal M\in\mathcal G_1}D(\mathcal N\|\mathcal M).$$
--
--   The optimized radii are finite, and the successive limits exist. This is the constant-channel divergence form of the AEP; it asserts nothing for a singleton alternative.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, PDF p. 15, Eq.(68): constant-channel divergence form of the AEP

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P65

noncomputable section

open Filter QAlgorithms

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Intakethird100.P65

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (transposeBob)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Independent2.P01 (dampingKraus damping)

open QAlgorithms.Papers.Independent.Gap48.P33 (phaseFlipChannel)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P62 (Stochastic)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized purifiedDistance)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer permute)

open QAlgorithms.Papers.Independent.Information100.P71 (diamond channelPower channelRelative)

open QAlgorithms.Papers.Independent.Support50.P39 (quantumMutualInformation)

variable {A B C D R : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty R]

/-- Eq.(68), PDF p.15: all possibly correlated block constant channels.
The extended inner radius is also explicitly finite before conversion to real. -/
theorem constantDivergence_aep (N : Superop A B) (hN : IsChannel N) :
    ∃ value : ℝ, constantRelativeRadius N = (value : EReal) ∧
      (∀ e : ℝ, 0 ≤ e → ∀ n : ℕ,
        constantMaxRadius (channelPower N n) e ≠ ⊤ ∧
        constantMaxRadius (channelPower N n) e ≠ ⊥) ∧
      IteratedLimit (fun e n => (constantMaxRadius (channelPower N n) e).toReal / n) value := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P65

end
