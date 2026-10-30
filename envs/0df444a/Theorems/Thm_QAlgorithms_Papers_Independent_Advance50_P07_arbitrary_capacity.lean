-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P07_arbitrary_capacity
-- name    : QAlgorithms.Papers.Independent.Advance50.P07.arbitrary_capacity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:31:35.438362+00:00
-- url     : https://prove2.me/theorems/51b80766-a5ef-4590-b782-c837f8b09fbd
-- title:
--   Arbitrary correlated-noise quantum capacity
-- statement:
--   Let $A$ and $B$ be fixed nonzero finite-dimensional registers, and let $\widehat\Phi=(\Phi_n)_{n\ge1}$ be any sequence of CPTP maps from $A^{\otimes n}$ to $B^{\otimes n}$. Define $Q_{\rm ent}^\infty$ by first taking the block-length liminf of $Q_{\rm ent}(\Phi_n;\epsilon)/n$, then letting $\epsilon\downarrow0$. For every sequence of nonzero input subspaces $\widehat S=(S_n)$, form the maximally entangled input of (16) and its computed output marginal $\widehat\omega_{\widehat S}^{RB}$. Then
--
--   $$Q_{\rm ent}^\infty(\widehat\Phi)=\max_{\widehat S}\underline I^c(\widehat\omega_{\widehat S}^{RB}),\qquad \underline I^c(\widehat\rho^{RB})=\min_{\widehat\sigma^B}\underline D(\widehat\rho^{RB}\Vert\widehat 1_R\otimes\widehat\sigma^B).$$
--
--   Each comparison $\sigma_n^B$ is a normalized state. Here $\underline D$ is the supremum of all real $\gamma$ for which $\liminf_n\operatorname{Tr}(\rho_n-2^{n\gamma}\sigma_n)_+=1$, with extended endpoints retained. The outer capacity limit exists, the subspace maximum is attained, and every comparison-sequence minimum is attained. This characterizes unassisted subspace transmission without assumptions on correlations between channel uses.
-- source:
--   The quantum capacity of channels with arbitrarily correlated noise, arXiv:0902.0158v5, PDF p. 13, Theorem 3 (arbitrary channels); original paper-result seed

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

/-- Theorem 3, PDF p.13: arbitrary correlated channels, without product,
stationarity, causality or forgetfulness premises. Maximizing subspace
sequences and spectral comparison minima are conclusions. -/
theorem arbitrary_capacity {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (Phi : (k : ℕ) → Superop (PositiveTensorBasis A k) (PositiveTensorBasis B k))
    (hPhi : ∀ k, IsChannel (Phi k)) :
    (∃ S : (k : ℕ) → Frame (PositiveTensorBasis A k),
      subspaceAsymptoticCapacity Phi false = infCoherent (fun k => frameOutput (Phi k) (S k)) ∧
      ∀ T : (k : ℕ) → Frame (PositiveTensorBasis A k),
        infCoherent (fun k => frameOutput (Phi k) (T k)) ≤
          infCoherent (fun k => frameOutput (Phi k) (S k))) ∧
    (∀ S : (k : ℕ) → Frame (PositiveTensorBasis A k),
      ∃ sigma : (k : ℕ) → {tau : Mat (PositiveTensorBasis B k) // Density tau},
        infCoherent (fun k => frameOutput (Phi k) (S k)) =
          comparisonInf (fun k => frameOutput (Phi k) (S k)) sigma) ∧
    Tendsto (capacityRate Phi false) (𝓝[>] (0 : ℝ)) (𝓝 (subspaceAsymptoticCapacity Phi false)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P07

end
