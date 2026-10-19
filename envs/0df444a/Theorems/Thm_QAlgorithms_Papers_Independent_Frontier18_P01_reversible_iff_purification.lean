-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P01_reversible_iff_purification
-- name    : QAlgorithms.Papers.Independent.Frontier18.P01.reversible_iff_purification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:48:43.546288+00:00
-- url     : https://prove2.me/theorems/8a64b79b-d6c6-418a-9d3b-d677983a1215
-- title:
--   Lemma 5: support-code reversibility iff one purification is recoverable
-- statement:
--   All Hilbert spaces are complex and separable, with completed Hilbert tensor products. States are positive trace-class operators of trace one, and channels are completely positive and trace preserving. Write $H$ for entropy and $D$ for relative entropy, using natural logarithms; $I(\rho,\Phi)$ is the relative entropy of the channel-applied purification against the product of its marginals. Let $\psi_{AR}$ be any fixed pure-state purification of $\rho$. Perfect reversibility on $\rho$ means that one CPTP decoder $\mathcal D:B\to A$ recovers every state supported in $\operatorname{supp}\rho$, including states with equal support. Then
--
--   $$\Phi\text{ is perfectly reversible on }\rho\quad\Longleftrightarrow\quad\exists\mathcal D:\ ((\mathcal D\circ\Phi)\otimes\operatorname{Id}_R)(\psi_{AR})=\psi_{AR}.$$
--
--   No entropy restriction is imposed. The equivalence identifies recovery of the whole support code with recovery of one purification.
-- source:
--   Mutual and coherent informations for infinite-dimensional quantum channels, arXiv:1004.2495v2, PDF p. 17, Lemma 5: support-code reversibility iff one purification is recoverable

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

noncomputable section

open Filter

open scoped ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P01

variable {I J K L E R : Type}

/-- Lemma 5, PDF pp.17,26: support-code recovery iff one given purification is
recoverable. No input entropy assumption, including the rank-one case. -/
theorem reversible_iff_purification [Countable I] [Countable J] [Countable R] (rho : State I) (Phi : Channel I J)
    (psi : PureState (I × R)) (hp : Purifies psi rho.coefficients) :
    PerfectlyReversible rho Phi ↔ ∃ D : Channel J I,
      tensorApply (D.val ∘ Phi.val) psi.val.coefficients = psi.val.coefficients := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P01

end
