-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_entanglementBreakingExponent
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.entanglementBreakingExponent
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:46:25.775516+00:00
-- url     : https://prove2.me/theorems/d6cf1093-585a-41a7-bf5a-465742db3fb4
-- title:
--   All-order subadditivity and exact exponent for entanglement-breaking channels
-- statement:
--   Let $\Phi:\mathcal L(H_{\rm in})\to\mathcal L(H_{\rm out})$ be a CPTP linear map between nonzero finite-dimensional complex Hilbert spaces. Its associated cq alphabet consists of all input density operators, and $\chi^*_\alpha(\Phi)$ is the supremum of first-type sandwiched information over all finite ensembles of such inputs. Its tensor channel is the full linear tensor extension. The operational exponent $\operatorname{sc}(R,\Phi)$ uses the two simultaneous liminf coding conditions of Definition V.1, with arbitrary, possibly entangled, input density operators for every blocklength and uniform-message average success. Write $H^*_{R,c}(\Phi)=\sup_{\alpha>1}(\alpha-1)\{R-\chi^*_\alpha(\Phi)\}/\alpha$.
--
--   Suppose $\Phi$ is entanglement breaking, equivalently in finite dimension it admits a finite measure-and-prepare form $\Phi(A)=\sum_j\operatorname{Tr}(AE_j)\tau_j$, with a POVM $(E_j)$ and density operators $(\tau_j)$. Then
--   $$\chi^*_\alpha(\Phi^{\otimes n})\le n\chi^*_\alpha(\Phi),\qquad n\in\mathbb N,\ \alpha>1,$$
--   and for every $R>0$,
--   $$\operatorname{sc}(R,\Phi)=H^*_{R,c}(\Phi).$$
--
--
--   This is the finite-dimensional unassisted classical-coding application. It asserts no adaptive LOCC or private-capacity bound.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 36, §VI A, unnumbered exact exponent for entanglement-breaking channels

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

/-- Unnumbered application §VI A, PDF p.36: all-order star subadditivity and
exact unassisted classical strong converse exponent of entanglement-breaking channels.
Codes may have entangled quantum input states. No adaptive/private claim is made. -/
theorem entanglementBreakingExponent [Nonempty I] [Nonempty J] (N : Superop I J) (hN : IsChannel N)
    (hEB : FiniteMeasurePrepare N) :
    (∀ a : ℝ, 1 < a → ∀ n : ℕ,
      quantumRenyiCapacity a (piSuperop (fun _ : Fin n => N)) ≤ (n : EReal) * quantumRenyiCapacity a N) ∧
    (∀ R : ℝ, 0 < R → quantumSc N R = converseCapacityTransform .star (associated N) R) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
