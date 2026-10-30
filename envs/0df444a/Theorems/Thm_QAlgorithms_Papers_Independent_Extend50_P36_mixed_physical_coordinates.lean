-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_mixed_physical_coordinates
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.mixed_physical_coordinates
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:13:09.141822+00:00
-- url     : https://prove2.me/theorems/e5541b70-c1ff-4c82-8837-f664fcaddf2d
-- title:
--   Appendix A, reproduced background: full physical mixed S3 coordinates and positivity
-- statement:
--   All operators below act on $(\mathbb C^d)^{\otimes3}$ with $d\ge2$. Write $A=V_{AB}$, $B=V_{BC}$, $C=V_{CA}$, $T=V_{ABC}$ for the actual tensor-factor permutations, and $T^\dagger=V_{CBA}$. For either basis $B_+,B_-,B_0,B_1,B_2,B_3$, define real coordinates by $r_k=\operatorname{Tr}(wB_k)$. The allowed coordinates satisfy
--   $$r_++r_-+r_0=1,\quad r_+,r_-,r_0\ge0,\quad r_1^2+r_2^2+r_3^2\le r_0^2,$$
--   with $r_-=0$ at $d=2$.
--
--   Use $A'=A^{T_A}$, $C'=C^{T_A}$, $T'=T^{T_A}$, $D'=(T^\dagger)^{T_A}$, where $T_A$ denotes transpose on factor A. Define
--   $$S_+=\tfrac12[I+B-(A'+C'+T'+D')/(d+1)],\quad S_-=\tfrac12[I-B+(T'+D'-A'-C')/(d-1)],$$
--   $$S_0=[d(A'+C')-(T'+D')]/(d^2-1),\quad S_1=[d(T'+D')-(A'+C')]/(d^2-1),$$
--   $$S_2=(A'-C')/\sqrt{d^2-1},\qquad S_3=i(T'-D')/\sqrt{d^2-1}.$$
--   The collectively $\overline U\otimes U\otimes U$ invariant density operators are exactly
--   $$w(s)=\frac{2s_+S_+}{d(d+2)(d-1)}+\frac{2s_-S_-}{d(d-2)(d+1)}+\frac1{2d}\sum_{k=0}^3s_kS_k$$
--   with the coordinate conditions above, replacing $r$ by $s$. At $d=2$ omit the $S_-$ summand and impose $s_-=0$. Reconstruction is a density operator if and only if these conditions hold, its coordinates recover $s$, and every invariant density operator reconstructs from its extracted coordinates.
--
--   This concerns the concrete three-factor physical representation.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 14, Appendix A, reproduced background: full physical mixed S3 coordinates and positivity

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Eqs.(A5)–(A7), PDF pp.14–15: complete physical mixed coordinate and PSD
characterization, for conjugate(U)⊗U⊗U, including the absent d=2 sector. -/
theorem mixed_physical_coordinates (d : ℕ) (hd : 2 ≤ d) :
    CoordinateCharacterization true d := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
