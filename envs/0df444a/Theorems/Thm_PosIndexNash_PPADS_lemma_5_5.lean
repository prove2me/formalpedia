-- Prove2me | Theorems.Thm_PosIndexNash_PPADS_lemma_5_5
-- name    : PosIndexNash.PPADS.lemma_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:32:22.631582+00:00
-- url     : https://prove2.me/theorems/9cbf3a3d-f8d3-4a2e-8717-420761d99704
-- title:
--   Lemma 5.5 — determinant identity det M_II = det(I_d − DΦ(λ)), hence sign det M_II = ind_Φ(λ)
-- statement:
--   Let a max-affine circuit in normal form with anchored outputs be strict at every fixed point, with $M = A - UV^\top$. For every solution $x$ of the LCP (39), with corresponding fixed point $\lambda = V^\top x$ and active set $I = \mathrm{supp}(x)$,
--   $$\det M_{II} = \det\big(I_d - D\Phi(\lambda)\big),$$
--   and moreover $\mathrm{sign}\det M_{II} = \mathrm{sign}\det(I_d - D\Phi(\lambda)) = \mathrm{ind}_\Phi(\lambda)$.
--
--   The identity carries the fixed point index into the LCP, where Lemma 6.5 turns it into the Shapley index.
--
--   Differences from the source:
--   - generalization: "$\Phi$ and its circuit from Theorem 4.2 (strict and regular at every fixed point)", in normal form → every anchored normal form that is strict at every fixed point, without regularity; reason: the identity needs only strictness (it makes $\Phi$ locally affine); the Theorem 4.2 circuit in normal form satisfies the hypotheses, so the statement specializes.
--   - encoding: $D\Phi(\lambda)$, the Jacobian of the active affine branch, and $M_{II}$ → `fderiv ℝ` of the normal form's map at $\lambda$, and the principal submatrix indexed by the subtype $\{i : x_i > 0\}$; reason: at a strict point the derivative is that of the active branch; a principal minor does not depend on the order of $I$.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), p. 38, Lemma 5.5

import Mathlib
import Definitions.Def_QuasiStrictNE_supp
import Definitions.Def_PosIndexNash_PPADS_NormalForm
import Definitions.Def_PosIndexNash_PPADS_LCP
import Definitions.Def_PosIndexNash_PPADS_FixedPointIndex

open Matrix

namespace PosIndexNash.PPADS

theorem lemma_5_5 (F : NormalForm) (hF : F.Anchored) (hstrict : F.StrictAtFixedPoints) :
    ∀ x ∈ LCPSol (F.M.map ((↑) : ℚ → ℝ)) (-(fun i => (F.b i : ℝ))),
      ((F.M.map ((↑) : ℚ → ℝ)).submatrix
          (Subtype.val : {i // i ∈ QuasiStrictNE.supp x} → Fin F.m) Subtype.val).det =
        detIdSubD F.Phi ((F.V.map ((↑) : ℚ → ℝ))ᵀ *ᵥ x) ∧
      SignType.sign ((F.M.map ((↑) : ℚ → ℝ)).submatrix
          (Subtype.val : {i // i ∈ QuasiStrictNE.supp x} → Fin F.m) Subtype.val).det =
        SignType.sign (detIdSubD F.Phi ((F.V.map ((↑) : ℚ → ℝ))ᵀ *ᵥ x)) ∧
      ((SignType.sign (detIdSubD F.Phi ((F.V.map ((↑) : ℚ → ℝ))ᵀ *ᵥ x)) : SignType) : ℤ) =
        fixedPointIndex F.Phi ((F.V.map ((↑) : ℚ → ℝ))ᵀ *ᵥ x) := by sorry

end PosIndexNash.PPADS
