-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P68_continuity_inside_distillable_region
-- name    : QAlgorithms.Papers.Independent.Intake100.P68.continuity_inside_distillable_region
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:05:27.815839+00:00
-- url     : https://prove2.me/theorems/9751eb13-f632-4397-b643-491adc376d0d
-- title:
--   Proposition 6 (abstract and main result): continuity inside the distillable region
-- statement:
--   Let $E$ be a finite real-valued functional on finite bipartite asymptotic resource products. Assume only that an actual asymptotic LOCC conversion $R^{\otimes x}\to S^{\otimes y}$, with $x>0$ and $y\ge0$, implies $yE(S)\le xE(R)$. Supplies mean independent integer copy counts with floors; conversion permits every positive error and rate slack, all sufficiently large block lengths, and unconditional normalized output. The same functional is used across positive finite local dimensions. Neither additivity nor continuity is assumed.
--
--   Fix positive finite local dimensions $a,b$. Let $\Gamma$ be open in the affine space of trace-one Hermitian operators, and suppose every element of $\Gamma$ is a density operator with positive distillable entanglement. Then
--
--   $$E|_{\Gamma}\text{ is continuous}.$$
--
--   The topology is equivalently that of trace distance $T(\rho,\sigma)=\tfrac12\operatorname{Tr}|\rho-\sigma|$. This is single-copy continuity at fixed dimensions; the affine-open convention excludes density-surface points. No ebit normalization or continuity of distillable entanglement is assumed.
--
--   This statement records the source result at fixed finite dimensions and can be reused with the same operational conversion convention.
-- source:
--   On the continuity of asymptotic measures of entanglement, arXiv:quant-ph/0203107v1, PDF p. 2, Proposition 6 (abstract and main result): continuity inside the distillable region

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P68

noncomputable section

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P68

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

/-- PDF pp.1–3, Proposition 6: continuity on affine-open sets entirely
of distillable densities. No ebit normalization or continuity of Ed is assumed.
The affine ambient space excludes the density surface as required on p.3. -/
theorem continuity_inside_distillable_region
    (E : SupplyProduct → ℝ) (hE : IsAsymptoticMeasure E)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (Gamma : Set (AffineState a b))
    (hopen : IsOpen Gamma)
    (hGamma : ∀ rho ∈ Gamma, IsDensityMatrix rho.val ∧ 0 < loccDistillable rho.val) :
    ContinuousOn (fun rho : AffineState a b => resourceSingleValue E rho.val) Gamma := by sorry

end QAlgorithms.Papers.Independent.Intake100.P68

end
