-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P15_erasure_syndrome_commutation
-- name    : QAlgorithms.Papers.Independent.Extend50.P15.erasure_syndrome_commutation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:58:39.861812+00:00
-- url     : https://prove2.me/theorems/5112b1d1-9429-45f1-843b-c73c25f50e51
-- title:
--   Flagged erasure syndrome measurements commute with transversal gates
-- statement:
--   Let $d\ge2$ and let $n\ge0$ be the number of sites. Each local output space is $\mathbb C^d\oplus\mathbb C|e\rangle$, where $|e\rangle$ is the orthogonal erasure flag. For a subset $s$ of erased sites, let $P_s$ project onto the sector with flags exactly on $s$. For $U\in\mathrm{SU}(d)$, choose a fixed subset of active sites and let $G_U$ apply $U\oplus1$ there and identity at idle sites. Then
--
--   $$P_sG_U=G_UP_s.$$
--
--   Moreover, any density matrix $\rho$ supported in that sector satisfies
--
--   $$P_s\rho P_s=\rho,\qquad P_sG_U\rho G_U^\dagger P_s=G_U\rho G_U^\dagger.$$
--
--   Thus recording the flagged erasure pattern does not disturb a state of known syndrome before or after a transversal gate. This is the algebraic basis of the source's delayed-recovery procedure.
-- source:
--   Optimal Universal Quantum Error Correction via Bounded Reference Frames, arXiv:2007.09154v2, PDF p. 8, Efficient error syndrome extraction

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P15

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P15

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P75 (Register)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Efficient syndrome extraction, PDF p.8. Flag measurements commute with every
maskedTransversalMatrix gate; a state in a known erasure sector is undisturbed, including after the
gate. This supplies the identity behind the four-step procedure, not a threshold theorem. -/
theorem erasure_syndrome_commutation (d n : ℕ) (hd : 2 ≤ d)
    (active : Fin n → Bool) (s : Finset (Fin n)) (U : (Matrix.specialUnitaryGroup (Fin d) ℂ)) :
    let P := erasurePatternProjector d n s
    let G := flaggedTransversal active (U : Matrix (Fin d) (Fin d) ℂ)
    P * G = G * P ∧
      ∀ rho : Matrix (FlaggedRegister d n) (FlaggedRegister d n) ℂ,
        IsDensityMatrix rho → P * rho * P = rho →
          conjSuperop P rho = rho ∧
          conjSuperop P (conjSuperop G rho) = conjSuperop G rho := by sorry

end QAlgorithms.Papers.Independent.Extend50.P15

end
