-- Prove2me | Theorems.Thm_P2M_DedekindZeta_Theta_eEmb__mem_idealLattice_iff_6d901df151c6
-- name    : P2M_DedekindZeta_Theta_eEmb__mem_idealLattice_iff_6d901df151c6
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:11:26.778863+00:00
-- url     : https://prove2.me/theorems/024118da-d240-410a-a5a2-fe0b3c9837e1
-- title:
--   P2 M Dedekind Zeta Theta e Emb  mem ideal Lattice iff 6d901df151c6: P2 M Dedekind Zeta Theta e Emb  mem ideal Lattice iff 6d901df151c6
-- statement:
--   The point `eEmbℝ η` lies in the ideal lattice `Λ(I)` iff `η` is the
--   `mixedEmbedding` image of some `b ∈ I`. (`eEmb K b = eEmbℝ K (mixedEmbedding K b)`
--   and `eEmbℝ` is a linear iso, so this is `mem_idealLattice_iff` transported through
--   `eEmbℝ`.)
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L594-L599
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L594-L599

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem P2M_DedekindZeta_Theta_eEmb__mem_idealLattice_iff_6d901df151c6 (I : FractionalIdeal (𝓞 K)⁰ K) (η : mixedSpace K) :
    eEmbℝ K η ∈ idealLattice K I ↔
      ∃ b ∈ (I : Submodule (𝓞 K) K), mixedEmbedding K b = η := by sorry

alias «DedekindZeta».«Theta».«eEmbℝ_mem_idealLattice_iff» := P2M_DedekindZeta_Theta_eEmb__mem_idealLattice_iff_6d901df151c6
