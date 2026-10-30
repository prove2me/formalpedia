-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_theoremVI1
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.theoremVI1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:39:22.140586+00:00
-- url     : https://prove2.me/theorems/d391aaf4-cee9-4fbf-9aba-8f578014e47e
-- title:
--   Quantum-channel exponent bounds and an equality criterion
-- statement:
--   Let $\Phi:\mathcal L(H_{\rm in})\to\mathcal L(H_{\rm out})$ be a CPTP linear map between nonzero finite-dimensional complex Hilbert spaces. Its associated cq alphabet consists of all input density operators, and $\chi^*_\alpha(\Phi)$ is the supremum of first-type sandwiched information over all finite ensembles of such inputs. Its tensor channel is the full linear tensor extension. The operational exponent $\operatorname{sc}(R,\Phi)$ uses the two simultaneous liminf coding conditions of Definition V.1, with arbitrary, possibly entangled, input density operators for every blocklength and uniform-message average success. Write $H^*_{R,c}(\Phi)=\sup_{\alpha>1}(\alpha-1)\{R-\chi^*_\alpha(\Phi)\}/\alpha$.
--
--   For every $R>0$,
--   $$\sup_{\alpha>1}\frac{\alpha-1}{\alpha}\left\{R-\limsup_{n\to\infty}\frac1n\chi^*_\alpha(\Phi^{\otimes n})\right\}
--   \le\operatorname{sc}(R,\Phi)\le H^*_{R,c}(\Phi).$$
--   If $\limsup_n n^{-1}\chi^*_\alpha(\Phi^{\otimes n})\le\chi^*_\alpha(\Phi)$ for every $\alpha>1$, then
--   $$\operatorname{sc}(R,\Phi)=H^*_{R,c}(\Phi).$$
--
--
--   The regularized lower bound includes entangled input ensembles; it is not a regularization of only product cq codewords.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 36, Theorem VI.1 For any quantum channel Φ and any rate R > 0,

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P45

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

open Filter Set

namespace QAlgorithms.Papers.Independent.Bridge50.P45

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch)

open QAlgorithms.Papers.Independent.Dependency50.P35 (lnOp)

open QAlgorithms.Papers.Independent.Next46.P23 (eigenvalues)

open QAlgorithms (spectralProjector)

variable {I : Type} [Fintype I] [DecidableEq I]

variable {X : Type} [Nonempty X] [Nonempty I]

variable {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]

/-- Theorem VI.1, PDF p.36: both bounds and the conditional equality.
The lower bound regularizes capacities of the FULL quantum tensor channel. -/
theorem theoremVI1 [Nonempty I] [Nonempty J] (N : Superop I J) (hN : IsChannel N) (R : ℝ) (hR : 0 < R) :
    (⨆ a : {a : ℝ // 1 < a}, (((a.1-1)/a.1 : ℝ) : EReal) *
      ((R : EReal) - Filter.limsup (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) *
        quantumRenyiCapacity a.1 (piSuperop (fun _ : Fin n => N))) atTop)) ≤ quantumSc N R ∧
    quantumSc N R ≤ converseCapacityTransform .star (associated N) R ∧
    ((∀ a : ℝ, 1 < a → Filter.limsup (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) *
      quantumRenyiCapacity a (piSuperop (fun _ : Fin n => N))) atTop ≤ quantumRenyiCapacity a N) →
        quantumSc N R = converseCapacityTransform .star (associated N) R) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
