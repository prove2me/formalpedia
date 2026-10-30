-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P13_character_cycle_expansion
-- name    : QAlgorithms.Papers.Independent.Extend50.P13.character_cycle_expansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:37:20.760008+00:00
-- url     : https://prove2.me/theorems/c8c96e97-d107-4040-8180-7e5f6b8786b7
-- title:
--   Observation 6: explicit character and cycle expansion
-- statement:
--   All matrices are complex, $d\times d$, with $d\ge1$. Write $I$ for the identity and $\operatorname{tr}$ for the ordinary, unnormalized trace. Matrix inequalities use the Löwner order, so $A\ge0$ includes Hermiticity. For $k=r+1\ge1$ and a partition $\lambda\vdash k$, let $T(\pi)$ permute tensor factors by $v_1\otimes\cdots\otimes v_k\mapsto v_{\pi^{-1}(1)}\otimes\cdots\otimes v_{\pi^{-1}(k)}$, and set $P_\lambda=\frac{\chi_\lambda(e)}{k!}\sum_{\pi\in S_k}\chi_\lambda(\pi^{-1})T(\pi)$ and $f_\lambda(X_1,\ldots,X_r)=\operatorname{tr}_{1\ldots r}[P_\lambda(X_1\otimes\cdots\otimes X_r\otimes I)]$. Here $\chi_\lambda$ is the character of the shape-labelled Specht representation, independently of $d$; shapes with more than $d$ rows are included. For each $\pi$, let $\sigma_1^\pi,\ldots,\sigma_{\ell_\pi}^\pi$ be its canonical cycles, largest element last and ordered by those largest elements. Put $\widetilde R_{\sigma_{\ell_\pi}^\pi}=R_{\sigma_{\ell_\pi}^\pi}(X_1,\ldots,X_r,I)$. Then
--
--   $$f_\lambda(X_1,\ldots,X_r)=\frac{\chi_\lambda(e)}{k!}\sum_{\pi\in S_k}\chi_\lambda(\pi^{-1})\left(\prod_{j<\ell_\pi}\operatorname{tr}(R_{\sigma_j^\pi})\right)\widetilde R_{\sigma_{\ell_\pi}^\pi}.$$
--
--   Singleton trace factors and empty products are retained. This gives an explicit trace-polynomial expansion of the normalized map.
-- source:
--   Positive maps and trace polynomials from the symmetric group, arXiv:2002.12887v2, PDF p. 10, Observation 6: explicit character and cycle expansion

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P13

attribute [local instance] Classical.propDecidable

/-- Observation 6, Eq.35 (PDF p.10). The sum uses the computed Specht character
and original factorial normalization. Inversion of permutations reindexes the sum;
symmetric-group characters are invariant under inversion. -/
theorem character_cycle_expansion {d r : ℕ} (hd : 0 < d)
    (lambda : QAlgorithms.Schur.Partition (r+1) (r+1)) (X : Fin r → (Matrix (Fin d) (Fin d) ℂ)) :
    polarizedMap lambda X =
      (QAlgorithms.Schur.spechtCharacter lambda 1 / ((r+1).factorial : ℂ)) •
        ∑ pi : Equiv.Perm (Fin (r+1)),
          QAlgorithms.Schur.spechtCharacter lambda pi⁻¹ •
            openCycleExpression pi (Fin.last r) (Fin.lastCases (1 : (Matrix (Fin d) (Fin d) ℂ)) X) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P13

end
