-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P39_holevo_radius_limits
-- name    : QAlgorithms.Papers.Independent.Bridge50.P39.holevo_radius_limits
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:49:12.816909+00:00
-- url     : https://prove2.me/theorems/0eccad5e-f369-4879-ad8d-ec347ec04cb6
-- title:
--   Two-sided limits of both sandwiched channel information quantities
-- statement:
--   Let $\mathcal N:A\to B$ be a quantum channel on positive, finite-dimensional complex Hilbert spaces. Let $\widetilde\chi_\alpha$ be the supremum over finite mixed-state input ensembles of the infimum, over output states $\sigma_B$, of the sandwiched divergence between the resulting classical-quantum output and its classical marginal tensored with $\sigma_B$. Let $\widetilde K_\alpha(\mathcal N)=\inf_{\sigma_B}\sup_{\rho_A}\widetilde D_\alpha(\mathcal N(\rho_A)\Vert\sigma_B)$. All states are normalized and logarithms are base two. The sandwiched divergence has generalized inverse powers on the support and is $+\infty$ on orthogonal states, or on unsupported first states when $\alpha>1$.
--
--   Write $H(\rho)=-\operatorname{Tr}(\rho\log_2\rho)$ and define the ordinary quantities by
--
--   $$
--   \chi(\mathcal N)=\sup_{\{p_x,\rho_x\}}\left[H\!\left(\sum_xp_x\mathcal N(\rho_x)\right)-\sum_xp_xH(\mathcal N(\rho_x))\right],\qquad
--   K(\mathcal N)=\inf_{\sigma_B}\sup_{\rho_A}D(\mathcal N(\rho_A)\Vert\sigma_B).
--   $$
--
--   Here $D$ is Umegaki relative entropy in bits, with value $+\infty$ on support failure. Both limits hold from both sides:
--
--   $$
--   \lim_{\alpha\uparrow1}\widetilde\chi_\alpha(\mathcal N)
--   =\lim_{\alpha\downarrow1}\widetilde\chi_\alpha(\mathcal N)=\chi(\mathcal N),\qquad
--   \lim_{\alpha\uparrow1}\widetilde K_\alpha(\mathcal N)
--   =\lim_{\alpha\downarrow1}\widetilde K_\alpha(\mathcal N)=K(\mathcal N).
--   $$
--
--   The left limits use $0<\alpha<1$ and the right limits use $\alpha>1$. These limits link the sandwiched information quantities to their ordinary counterparts, without restricting comparison states to full rank.
-- source:
--   Strong converse exponents for the feedback-assisted classical capacity of entanglement-breaking channels, arXiv:1506.02228v4, PDF p. 10, Lemma 4, (4.26)-(4.28); Appendix C

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P39

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P39

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (relativeD tensorAction)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB ordinaryClassicalCapacity)

open QAlgorithms.Papers.Independent.Information100.P08 (channelHolevo)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Support50.P19
  (channelInformation informationRadius expTwo)

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- PDF pp.10-11, Lemma 4, (4.26)-(4.28), Appendix C pp.18-21:
both one-sided limits of both quantities, on distinct input and output spaces. -/
theorem holevo_radius_limits [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) :
    Tendsto (fun a : ℝ => channelInformation true a N)
      (nhdsWithin 1 (Set.Ioo 0 1)) (nhds (channelHolevo N : EReal)) ∧
    Tendsto (fun a : ℝ => channelInformation true a N)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (channelHolevo N : EReal)) ∧
    Tendsto (fun a : ℝ => informationRadius true a N)
      (nhdsWithin 1 (Set.Ioo 0 1)) (nhds (ordinaryRadius N)) ∧
    Tendsto (fun a : ℝ => informationRadius true a N)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (ordinaryRadius N)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P39

end
