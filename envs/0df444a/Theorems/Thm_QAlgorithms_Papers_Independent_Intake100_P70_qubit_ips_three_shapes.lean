-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_qubit_ips_three_shapes
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.qubit_ips_three_shapes
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:51:07.966671+00:00
-- url     : https://prove2.me/theorems/3ae99130-e953-4c75-8a28-55fcd207ef4e
-- title:
--   Example 13: exhaustive qubit IPS shapes
-- statement:
--   Let $\mathcal E$ be a CPTP qubit channel and $C$ a maximum convex preserved code in the isometric order. Write $\mathcal D_2$ for all qubit density matrices, $\mathcal D_{\mathrm{diag}}$ for those diagonal in the computational basis, and $I_2$ for the identity. Then
--
--   $$C\simeq_1\mathcal D_2\quad\text{or}\quad C\simeq_1\mathcal D_{\mathrm{diag}}\quad\text{or}\quad C\simeq_1\{I_2/2\}.$$
--
--   These are shapes $\{2\}$, $\{1,1\}$ and $\{1\}$. This classifies entire IPS shapes and does not forbid preserved proper subsets.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 11, Example 13: exhaustive qubit IPS shapes

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P70

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intake100.P70

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

/-- PDF p.11, Example 13: exhaustive algebraic shapes of maximum qubit codes.
The three state sets represent M2, diagonal matrices, and scalar identity.
Arbitrary proper disks or other subcodes are not ruled out as preserved subsets. -/
theorem qubit_ips_three_shapes (E : Superop (Fin 2) (Fin 2)) (hE : IsChannel E)
    (C : Set (Op (Fin 2))) (hC : MaximumCode (Preserved E) C) :
    OneIsometric C {rho : Op (Fin 2) | IsDensityMatrix rho} ∨
    OneIsometric C {rho : Op (Fin 2) | IsDensityMatrix rho ∧ ∀ i j, i ≠ j → rho i j = 0} ∨
    OneIsometric C {((1 / 2 : ℂ) • (1 : Op (Fin 2)))} := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
