-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P26_channel_radius
-- name    : QAlgorithms.Papers.Independent.Claimed50.P26.channel_radius
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:59:39.231795+00:00
-- url     : https://prove2.me/theorems/3b49a58c-99d7-4d55-b107-303b8d9ea7f8
-- title:
--   Lemma I.3 (radius inequalities and covariant-channel equalities)
-- statement:
--   Let $\Phi$ be a channel between nonzero finite-dimensional spaces and let $\alpha>1$. Let $D_\alpha$ be the Petz divergence in bits, extended to $+\infty$ on support failure. Define $r_{\rm out}$ by minimizing $\max_\rho D_\alpha(\Phi(\rho)\Vert\sigma)$ over all output density matrices $\sigma$, and define $r_{\rm im}$ by restricting the center to $\sigma=\Phi(\tau)$ for an input density matrix $\tau$. Then
--
--   $$
--   r_{\rm out}\le\chi_\alpha^*(\Phi)\le r_{\rm im}.
--   $$
--
--   Both outer minima and the inner maxima are attained. If $\Phi$ is covariant under continuous unitary representations of a compact group with irreducible output representation, then, writing $d_{\rm out}=\dim H_{\rm out}$,
--
--   $$
--   \chi_\alpha^*(\Phi)=r_{\rm out}=r_{\rm im}
--   =\log_2d_{\rm out}-S_\alpha^{\min}(\Phi).
--   $$
--
--   No irreducibility of the input representation is assumed. The identities connect the channel information radius to its constructed minimum output entropy.
-- source:
--   A strong converse for classical channel coding using entangled inputs, arXiv:0903.2838v1, PDF p. 5, Lemma I.3 (radius inequalities and covariant-channel equalities)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P26

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate Topology

open Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P26

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage depolarizing)

open QAlgorithms.Papers.Independent.Information100.P71
  (supportPower channelPower)

open QAlgorithms.Papers.Independent.Dependency50.P23
  (UACode uaCodeSuccess uaSuccess ordinaryClassicalCapacity)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Dependency50.P35 (renyiEntropy petz relative)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

/-- PDF pp.5–6, Lemma I.3: general inequalities, attained extrema, and every
covariant equality. No unitality or irreducibility of the input is imposed. -/
theorem channel_radius {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (Phi : Superop I J) (hPhi : IsChannel Phi) (alpha : ℝ) (ha : 1 < alpha) :
    outputRadius alpha Phi ≤ (channelChi alpha Phi : EReal) ∧
    (channelChi alpha Phi : EReal) ≤ imageRadius alpha Phi ∧ RadiiAttained alpha Phi ∧
    (CovariantIrreducible Phi →
      (channelChi alpha Phi : EReal) = outputRadius alpha Phi ∧
      outputRadius alpha Phi = imageRadius alpha Phi ∧
      channelChi alpha Phi = Real.logb 2 (Fintype.card J) - minOutput alpha Phi) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P26

end
