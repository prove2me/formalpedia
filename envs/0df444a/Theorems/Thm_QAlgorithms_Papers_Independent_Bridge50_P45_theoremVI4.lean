-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_theoremVI4
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.theoremVI4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:40:57.238976+00:00
-- url     : https://prove2.me/theorems/ee124470-f0ed-4766-bd65-c5ba60748e8f
-- title:
--   Exact exponent of KW-class channels
-- statement:
--   Let $\Phi:\mathcal L(H_{\rm in})\to\mathcal L(H_{\rm out})$ be a CPTP linear map between nonzero finite-dimensional complex Hilbert spaces. Its associated cq alphabet consists of all input density operators, and $\chi^*_\alpha(\Phi)$ is the supremum of first-type sandwiched information over all finite ensembles of such inputs. Its tensor channel is the full linear tensor extension. The operational exponent $\operatorname{sc}(R,\Phi)$ uses the two simultaneous liminf coding conditions of Definition V.1, with arbitrary, possibly entangled, input density operators for every blocklength and uniform-message average success. Write $H^*_{R,c}(\Phi)=\sup_{\alpha>1}(\alpha-1)\{R-\chi^*_\alpha(\Phi)\}/\alpha$.
--
--   Assume there are a compact topological group $G$ and continuous unitary representations $U_{\rm in},U_{\rm out}$ such that $U_{\rm out}$ is irreducible and $\Phi(U_{\rm in}(g)AU_{\rm in}(g)^*)=U_{\rm out}(g)\Phi(A)U_{\rm out}(g)^*$ for every $g,A$. No input irreducibility is required. Put $H_\alpha(\omega)=(1-\alpha)^{-1}\log\operatorname{Tr}\omega^\alpha$ away from one, $H_1(\omega)=-\operatorname{Tr}\omega\widehat{\log}\omega$, and $H_\alpha^{\min}(\Phi)=\min_{\rho\in\mathcal S(H_{\rm in})}H_\alpha(\Phi(\rho))$.
--
--   Assume in addition the KW property $H_\alpha^{\min}(\Phi^{\otimes n})=nH_\alpha^{\min}(\Phi)$ for every $\alpha>1$ and every $n\in\mathbb N$. For every $R>0$,
--   $$\operatorname{sc}(R,\Phi)=H^*_{R,c}(\Phi)
--   =\sup_{\alpha>1}\frac{\alpha-1}{\alpha}\{R-\log\dim H_{\rm out}+H_\alpha^{\min}(\Phi)\}.$$
--
--
--   Only the above-one additivity actually supplied by the KW definition is used; no below-one claim from VI.3 is assumed.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 38, Theorem VI.4 For any quantum channel Φ in the KW-class, and any rate R > 0,

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

/-- Theorem VI.4, PDF p.38: KW means compact covariance with irreducible output
and entropy additivity at all orders above one. Both exponent formulas are retained. -/
theorem theoremVI4 [Nonempty I] [Nonempty J] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (N : Superop I J) (hN : IsChannel N)
    (Uin : G →* Matrix.unitaryGroup I ℂ) (Uout : G →* Matrix.unitaryGroup J ℂ)
    (hcin : Continuous Uin) (hcout : Continuous Uout) (hcov : IrreducibleOutputCovariance N Uin Uout)
    (hadd : KWAdditive N) (R : ℝ) (hR : 0 < R) :
    quantumSc N R = converseCapacityTransform .star (associated N) R ∧
    quantumSc N R = (⨆ a : {a : ℝ // 1 < a}, (((a.1-1)/a.1 : ℝ) : EReal) *
      ((R : EReal) - (Real.log (Fintype.card J) : EReal) + minOutputEntropy a.1 N)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
