-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_cq_hadamard_diagonal
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.cq_hadamard_diagonal
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:06:52.47651+00:00
-- url     : https://prove2.me/theorems/6f9b2a26-d73e-4b29-9f0d-4adbd1d099cb
-- title:
--   Unnumbered: pure-preparation CQ conjugates are Hadamard diagonal
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. Let $w_j$ be an orthonormal input basis, $U$ the unitary with columns $w_j$, and $x_j$ unit output vectors. For Kraus operators $|x_j\rangle\langle w_j|$ and $X_{jk}=\langle x_k|x_j\rangle$,
--
--   $$
--   \Phi^C(\rho)=X\mathbin{*}(U^\dagger\rho U).
--   $$
--
--   The conjugate has simultaneously diagonal Kraus operators when inputs are expressed in that basis. No CPT extremality claim is used.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 11, Unnumbered: pure-preparation CQ conjugates are Hadamard diagonal

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P36

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Claimed50.P48

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P03 (convexRoof)

open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D E K L A2 B2 C2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

variable [Fintype L] [DecidableEq L] [Fintype A2] [DecidableEq A2]

variable [Fintype B2] [DecidableEq B2] [Fintype C2] [DecidableEq C2]

/-- Unnumbered CQ assertion, PDF pp.11–12: only the structural diagonal conclusion.
No claim of extremality among all CPT maps is made.
Correction: printed <x_j|x_k> becomes <x_k|x_j>, forced by tracing
|x_j><x_k| in (23), with no other change to the CQ data. -/
theorem cq_hadamard_diagonal [Nonempty A] [Nonempty B]
    (U : Matrix.unitaryGroup A ℂ) (x : A → EuclideanSpace ℂ B)
    (hx : ∀ k, IsState (x k)) :
    let F := rankOneKraus (basisColumns U) x
    complementaryChannel (indexedKrausDilation F) =
      (fun rho => Matrix.hadamard (gram x) ((U : Matrix A A ℂ)ᴴ * rho * (U : Matrix A A ℂ))) ∧
    ∃ r : ℕ, ∃ R : Fin r → Matrix A A ℂ,
      (∀ m i j, i ≠ j → R m i j = 0) ∧
      complementaryChannel (indexedKrausDilation F) =
        (fun rho => krausApply R ((U : Matrix A A ℂ)ᴴ * rho * (U : Matrix A A ℂ))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
