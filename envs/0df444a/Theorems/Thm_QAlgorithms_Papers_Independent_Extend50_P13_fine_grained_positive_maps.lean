-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P13_fine_grained_positive_maps
-- name    : QAlgorithms.Papers.Independent.Extend50.P13.fine_grained_positive_maps
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:44:37.085649+00:00
-- url     : https://prove2.me/theorems/f51b274f-1b6a-4b04-b89e-44e2266422e3
-- title:
--   Eq.(54): four fine-grained positive maps
-- statement:
--   All matrices are complex, $d\times d$, with $d\ge1$. Write $I$ for the identity and $\operatorname{tr}$ for the ordinary, unnormalized trace. Matrix inequalities use the Löwner order, so $A\ge0$ includes Hermiticity. For $X,Y\ge0$, each of the following four matrices is positive semidefinite:
--
--   $$\begin{aligned}
--   F_0&=[2\operatorname{tr}X\operatorname{tr}Y+2\operatorname{tr}(XY)]I-\operatorname{tr}(X)Y-\operatorname{tr}(Y)X-XY-YX,\\
--   F_1&=[2\operatorname{tr}X\operatorname{tr}Y-2\operatorname{tr}(XY)]I+\operatorname{tr}(X)Y+\operatorname{tr}(Y)X-XY-YX,\\
--   F_2&=[2\operatorname{tr}X\operatorname{tr}Y-\operatorname{tr}(XY)]I+2\operatorname{tr}(X)Y-\operatorname{tr}(Y)X-XY-YX,\\
--   F_3&=[2\operatorname{tr}X\operatorname{tr}Y+\operatorname{tr}(XY)]I-2\operatorname{tr}(X)Y+\operatorname{tr}(Y)X-XY-YX.
--   \end{aligned}$$
--
--   Writing $T_{ab}=T((ab))$ and $C=T((123))+T((132))$, the physical operators
--
--   $$E_{0,1}=\tfrac16[2I\mathbin{\pm}(2T_{12}-T_{13}-T_{23})-C],\quad E_{2,3}=\tfrac16[2I\mathbin{\pm}(2T_{23}-T_{12}-T_{13})-C]$$
--
--   are Hermitian idempotents, with $E_0+E_1=E_2+E_3=P_{(2,1)}$ and both products in either pair zero. Their contractions against $(X,Y)$ equal $F_i(X,Y)/6$ for arbitrary complex inputs. Any mixed vertical tensor product of these four maps is positive on globally PSD input pairs, including heterogeneous dimensions and zero parties. These are the two fine-grained orthogonal decompositions behind the four inequalities.
-- source:
--   Positive maps and trace polynomials from the symmetric group, arXiv:2002.12887v2, PDF p. 13, Eq.(54): four fine-grained positive maps

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P13

attribute [local instance] Classical.propDecidable

/-- Eq.54 and both orthogonal projector decompositions (PDF p.13). Every formula
is six times its normalized contraction. The later prose omits a factor two in
adding the displayed unscaled polynomials; that erroneous equality is not used. -/
theorem fine_grained_positive_maps
    (lambda : QAlgorithms.Schur.Partition 3 3) (hshape : lambda.val.rowLens = [2,1]) :
    (∀ (d : ℕ), 0 < d →
      (∀ i : Fin 4, (fineProjector d i).IsHermitian ∧
        fineProjector d i * fineProjector d i = fineProjector d i ∧
        (∀ X Y : (Matrix (Fin d) (Fin d) ℂ), contractInputs (fineProjector d i) ![X,Y] =
          (1/6 : ℂ) • finePolynomial i X Y) ∧
        (∀ X Y : (Matrix (Fin d) (Fin d) ℂ), X.PosSemidef → Y.PosSemidef →
          (finePolynomial i X Y).PosSemidef)) ∧
      fineProjector d 0 + fineProjector d 1 = centralProjector d lambda ∧
      fineProjector d 0 * fineProjector d 1 = 0 ∧
      fineProjector d 1 * fineProjector d 0 = 0 ∧
      fineProjector d 2 + fineProjector d 3 = centralProjector d lambda ∧
      fineProjector d 2 * fineProjector d 3 = 0 ∧
      fineProjector d 3 * fineProjector d 2 = 0) ∧
    (∀ (n : ℕ) (dims : Fin n → ℕ), (∀ j, 0 < dims j) →
      ∀ (choice : Fin n → Fin 4) (X Y : (Matrix ((∀ j, Fin (dims j))) ((∀ j, Fin (dims j))) ℂ)),
      X.PosSemidef → Y.PosSemidef →
      (contractInputs (verticalOperators dims (fun j => fineProjector (dims j) (choice j)))
        ![X,Y]).PosSemidef) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P13

end
