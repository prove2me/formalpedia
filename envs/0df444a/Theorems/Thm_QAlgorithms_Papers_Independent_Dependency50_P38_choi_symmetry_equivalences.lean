-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P38_choi_symmetry_equivalences
-- name    : QAlgorithms.Papers.Independent.Dependency50.P38.choi_symmetry_equivalences
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:14:04.107873+00:00
-- url     : https://prove2.me/theorems/588ffd03-4380-41d1-ab56-5aa735f8e77c
-- title:
--   Choi commutants characterize both channel symmetries
-- statement:
--   Let $d>0$ and $m,n\geq0$ be integers, and let $\Phi$ be a complex-linear completely positive trace-preserving map from operators on $(\mathbb C^d)^{\otimes m}$ to operators on $(\mathbb C^d)^{\otimes n}$. Use the unnormalized input-first Choi matrix $C_\Phi=\sum_{i,j}|i\rangle\langle j|\otimes\Phi(|i\rangle\langle j|)$ in the fixed computational bases. Then the following two equivalences hold:
--
--   $$
--   \begin{aligned}
--   &\bigl[\forall U\in SU(d),\ \forall A,\ \Phi(U^{\otimes m}A(U^{\otimes m})^*)=U^{\otimes n}\Phi(A)(U^{\otimes n})^*\bigr]\\
--   &\qquad\Longleftrightarrow\bigl[\forall U\in SU(d),\ (\overline U^{\otimes m}\otimes U^{\otimes n})C_\Phi=C_\Phi(\overline U^{\otimes m}\otimes U^{\otimes n})\bigr],\\
--   &\bigl[\forall\sigma\in S_m,\ \forall\tau\in S_n,\ \forall A,\ \Phi(P_\sigma A P_\sigma^*)=\Phi(A)=P_\tau\Phi(A)P_\tau^*\bigr]\\
--   &\qquad\Longleftrightarrow\bigl[\forall\sigma\in S_m,\ \forall\tau\in S_n,\ (\overline{P_\sigma}\otimes P_\tau)C_\Phi=C_\Phi(\overline{P_\sigma}\otimes P_\tau)\bigr].
--   \end{aligned}
--   $$
--
--   Here $A$ ranges over all input operators, and $P_\sigma$ permutes tensor factors by $|i_1,\ldots,i_m\rangle\mapsto|i_{\sigma^{-1}(1)},\ldots,i_{\sigma^{-1}(m)}\rangle$. The input and output permutations are independent. This identifies the precise commutants used in the paper's classification.
-- source:
--   Classification and implementation of unitary-equivariant and permutation-invariant quantum channels, arXiv:2510.08154v1, PDF p. 16, Proposition 4

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P38

open scoped Matrix ComplexConjugate

/-- arXiv:2510.08154v1, PDF p.16, Proposition 4, Eqs.(41)-(42), with
Definition 1 on p.5. Both equivalences hold on all operators. The input
representation in the Choi commutant is complex conjugated; input and output
permutations act independently. The local dimension is positive; copy counts
may be zero. `IsChannel` supplies finite-dimensional complex-linear CPTP maps. -/
theorem choi_symmetry_equivalences (d m n : ℕ) (hd : 0 < d)
    (Phi : Superop (Fin m → Fin d) (Fin n → Fin d)) (hPhi : IsChannel Phi) :
    ((∀ (U : Matrix.specialUnitaryGroup (Fin d) ℂ)
        (A : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ),
        Phi (piKron m (U : Matrix (Fin d) (Fin d) ℂ) * A *
          (piKron m (U : Matrix (Fin d) (Fin d) ℂ))ᴴ) =
        piKron n (U : Matrix (Fin d) (Fin d) ℂ) * Phi A *
          (piKron n (U : Matrix (Fin d) (Fin d) ℂ))ᴴ) ↔
      ∀ U : Matrix.specialUnitaryGroup (Fin d) ℂ,
        Commute
          (Matrix.kronecker
            ((piKron m (U : Matrix (Fin d) (Fin d) ℂ)).map (starRingEnd ℂ))
            (piKron n (U : Matrix (Fin d) (Fin d) ℂ)))
          (QAlgorithms.Papers.Independent.Information100.P34.choi Phi)) ∧
    ((∀ (sigma : Equiv.Perm (Fin m)) (tau : Equiv.Perm (Fin n))
        (A : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ),
        Phi (Schur.tensorPermutation d m sigma * A *
          (Schur.tensorPermutation d m sigma)ᴴ) = Phi A ∧
        Schur.tensorPermutation d n tau * Phi A *
          (Schur.tensorPermutation d n tau)ᴴ = Phi A) ↔
      ∀ (sigma : Equiv.Perm (Fin m)) (tau : Equiv.Perm (Fin n)),
        Commute
          (Matrix.kronecker
            ((Schur.tensorPermutation d m sigma).map (starRingEnd ℂ))
            (Schur.tensorPermutation d n tau))
          (QAlgorithms.Papers.Independent.Information100.P34.choi Phi)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P38

end
