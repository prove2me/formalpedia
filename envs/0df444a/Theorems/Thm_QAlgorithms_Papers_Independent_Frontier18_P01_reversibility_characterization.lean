-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P01_reversibility_characterization
-- name    : QAlgorithms.Papers.Independent.Frontier18.P01.reversibility_characterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:49:38.810141+00:00
-- url     : https://prove2.me/theorems/c43a39a6-0939-42d5-a18f-34abe1a87351
-- title:
--   Proposition 2: entropy saturation characterizes perfect reversibility
-- statement:
--   All Hilbert spaces are complex and separable, with completed Hilbert tensor products. States are positive trace-class operators of trace one, and channels are completely positive and trace preserving. Write $H$ for entropy and $D$ for relative entropy, using natural logarithms; $I(\rho,\Phi)$ is the relative entropy of the channel-applied purification against the product of its marginals. Suppose $H(\rho)<\infty$ and $\Phi,\widetilde\Phi$ are complementary through one isometry. Perfect reversibility on $\rho$ means existence of one CPTP decoder recovering every state supported within $\operatorname{supp}\rho$. Then
--
--   $$\begin{aligned}\Phi\text{ is perfectly reversible on }\rho&\Longleftrightarrow I_c(\rho,\Phi)=H(\rho),\\ \Phi\text{ is perfectly reversible on }\rho&\Longleftrightarrow I(\rho,\widetilde\Phi)=0.\end{aligned}$$
--
--   Thus either numerical saturation condition characterizes full support-code recovery.
-- source:
--   Mutual and coherent informations for infinite-dimensional quantum channels, arXiv:1004.2495v2, PDF p. 17, Proposition 2: entropy saturation characterizes perfect reversibility

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

noncomputable section

open Filter

open scoped ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P01

variable {I J K L E R : Type}

/-- Proposition 2, PDF pp.17–18: both equivalent numerical criteria and the
full support-code decoder property, under finite input entropy only. -/
theorem reversibility_characterization [Countable I] [Countable J] [Countable E] (rho : State I) (Phi : Channel I J)
    (Psi : Channel I E) (hcomp : Complementary Phi Psi) (hin : homogeneousEntropy rho.coefficients < ⊤) :
    (PerfectlyReversible rho Phi ↔ finiteInputCoherentInfo rho.coefficients Phi.val =
      (homogeneousEntropy rho.coefficients).toReal) ∧
    (PerfectlyReversible rho Phi ↔ mutualInformation rho.coefficients Psi.val = 0) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P01

end
