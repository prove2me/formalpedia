-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P46_validProcess_iff_constraints
-- name    : QAlgorithms.Papers.Independent.Intake100.P46.validProcess_iff_constraints
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:10:40.014149+00:00
-- url     : https://prove2.me/theorems/a47fd657-c5d5-4b3c-956b-eb08cb5af019
-- title:
--   Complete finite bipartite process normalization constraints
-- statement:
--   All systems have positive finite dimensions and fixed computational bases. Choi operators are unnormalized and input first. A valid process maps every pair of local CPTP maps, with arbitrary ancillary input and output wires, to a CPTP map. Purity tests every compatible pair of local unitaries with those same ancillary extensions.
--
--   Let $W$ be any complex matrix on $P A_I A_O B_I B_O F$. For a collection of wires $X$, write ${}_XW=(I_X/d_X)\otimes\operatorname{tr}_XW$, reinserted in the original wire order. Define
--
--   $$\begin{aligned}L_V(W)={}&W-{}_FW+{}_{A_OF}W+{}_{B_OF}W-{}_{A_OB_OF}W-{}_{A_IA_OF}W+{}_{A_IA_OB_OF}W\\&-{}_{B_IB_OF}W+{}_{A_OB_IB_OF}W-{}_{A_IA_OB_IB_OF}W+{}_{PA_IA_OB_IB_OF}W.\end{aligned}$$
--
--   Then the independently defined operational process predicate satisfies
--
--   $$W\text{ is valid}\quad\Longleftrightarrow\quad W\succeq0,\quad\operatorname{tr}W=d_Pd_{A_O}d_{B_O},\quad W=L_V(W).$$
--
--   This supplies both directions of the general bipartite process normalization interface. Validity is defined by ancillary CPTP tests, rather than by the three constraints on the right.
--
--   In addition, $L_V$ is self-adjoint for the Hilbert–Schmidt pairing $\langle X,Y\rangle=\sum_{i,j}\overline{X_{ij}}Y_{ij}$, satisfies $L_V^2=L_V$, and has image exactly the intersection of Eqs.(59)–(62): ${}_{B_IB_OF}X={}_{A_OB_IB_OF}X$, ${}_{A_IA_OF}X={}_{A_IA_OB_OF}X$, ${}_FX={}_{A_OF}X+{}_{B_OF}X-{}_{A_OB_OF}X$, and ${}_{A_IA_OB_IB_OF}X={}_{PA_IA_OB_IB_OF}X$.
-- source:
--   A purification postulate for quantum mechanics with indefinite causal order, arXiv:1611.08535v4, PDF p. 12, Appendix C, Eqs.(64)–(67)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P46

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Intake100.P46

/-- PDF pp.11–12, Appendix C, Eqs.(59)–(67): operational validity is equivalent to
positivity, the stated unnormalized trace, and the explicit finite linear projector.
The projector is Hilbert–Schmidt self-adjoint and idempotent, and its image is exactly
the intersection of the four linear constraint spaces (59)–(62). -/
theorem validProcess_iff_constraints {d : ProcessWireDimensions} (W : ProcessMatrix d) :
    (IsValidProcess W ↔ W.PosSemidef ∧
      Matrix.trace W = ((d 0 : ℕ) * (d 2 : ℕ) * (d 4 : ℕ) : ℂ) ∧
      W = validSubspaceProjector W) ∧
    (∀ X Y : ProcessMatrix d,
      (∑ i, ∑ j, conj (X i j) * validSubspaceProjector Y i j) =
      ∑ i, ∑ j, conj (validSubspaceProjector X i j) * Y i j) ∧
    (∀ X : ProcessMatrix d,
      validSubspaceProjector (validSubspaceProjector X) = validSubspaceProjector X) ∧
    (∀ X : ProcessMatrix d,
      (∃ Y : ProcessMatrix d, validSubspaceProjector Y = X) ↔
        replaceWires {3,4,5} X = replaceWires {2,3,4,5} X ∧
        replaceWires {1,2,5} X = replaceWires {1,2,4,5} X ∧
        replaceWires {5} X = replaceWires {2,5} X + replaceWires {4,5} X -
          replaceWires {2,4,5} X ∧
        replaceWires {1,2,3,4,5} X = replaceWires {0,1,2,3,4,5} X) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P46

end
