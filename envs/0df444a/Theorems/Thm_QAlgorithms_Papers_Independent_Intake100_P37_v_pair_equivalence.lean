-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P37_v_pair_equivalence
-- name    : QAlgorithms.Papers.Independent.Intake100.P37.v_pair_equivalence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:08:56.583645+00:00
-- url     : https://prove2.me/theorems/d4f72176-39ff-4b8a-9d07-224af454601d
-- title:
--   Exact equivalence between antisymmetric V pairs and Lambda atoms
-- statement:
--   Use $A$ fixed ordered pairs of V atoms, with excited doublet $e_1,e_2$, one ground level $g$, and real equal coupling $\gamma$ to the two field modes. Define the pair isometry $T$ by
--
--   $$
--   T(e)=\frac{|e_1e_2\rangle-|e_2e_1\rangle}{\sqrt2},\quad
--   T(g_1)=\frac{|ge_2\rangle-|e_2g\rangle}{\sqrt2},\quad
--   T(g_2)=\frac{|e_1g\rangle-|ge_1\rangle}{\sqrt2}.
--   $$
--
--   The photon-preserving tensor product $E=T^{\otimes A}$ embeds the full Lambda energy sector into the full $2A$-atom V energy sector and is isometric. The physical V Hamiltonian is Hermitian and
--
--   $$
--   H_VE=EH_\Lambda,\qquad e^{-itH_V}E=Ee^{-itH_\Lambda}.
--   $$
--
--   For every normalized $m$-photon input, the product-of-singlets V input has unit norm, and its full evolved vector is exactly $E\Psi_\Lambda(t)$. Its nonzero components have between $m$ and $m+A$ photons, while the full conserved V energy is $m+2A$. For every output increment $l$, tracing out the physical V atoms gives the same photonic instrument branch as the Lambda device. This transfers the cloning properties to the specified entangled V-pair preparation.
-- source:
--   Lambda's, V's and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, PDF p. 6, Sec. III, Eqs.(22)-(26)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P37

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.6-7 Eqs.(22)-(26): explicit antisymmetric pair isometry and
Hamiltonian/evolution intertwining on full physical sectors. There are 2A V
atoms versus A Lambda atoms, with conserved energies m+2A and m+A. -/
theorem v_pair_equivalence (A m : ℕ) (gamma t : ℝ) :
    (vH A m gamma).IsHermitian ∧
    pairKetᴴ * pairKet = 1 ∧
    (pairEmbedding A m)ᴴ * pairEmbedding A m = 1 ∧
    vH A m gamma * pairEmbedding A m = pairEmbedding A m * physicalH 2 A m gamma ∧
    QAlgorithms.Papers.Independent.Claimed50.P15.propagator (vH A m gamma) t * pairEmbedding A m =
      pairEmbedding A m * QAlgorithms.Papers.Independent.Claimed50.P15.propagator (physicalH 2 A m gamma) t ∧
    (∀ psi : EuclideanSpace ℂ (Fin 2), IsState psi →
      IsState (vInput A m psi) ∧
      vOutput A m gamma t psi = applyMatrix (pairEmbedding A m) (physicalOutput A m gamma t psi) ∧
      ∀ p : VBasis A m, vOutput A m gamma t psi p ≠ 0 →
        m ≤ (∑ a, (p.val.1 a).val) ∧ (∑ a, (p.val.1 a).val) ≤ m + A) ∧
    (∀ l : ℕ, vBranch A m l gamma t = physicalBranch A m l gamma t) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P37

end
