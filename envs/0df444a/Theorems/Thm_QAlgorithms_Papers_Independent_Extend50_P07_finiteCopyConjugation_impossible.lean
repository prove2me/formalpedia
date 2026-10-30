-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P07_finiteCopyConjugation_impossible
-- name    : QAlgorithms.Papers.Independent.Extend50.P07.finiteCopyConjugation_impossible
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:51:34.911865+00:00
-- url     : https://prove2.me/theorems/893046d4-5330-4d7e-8a4e-fd1a0840d529
-- title:
--   §4.1 proof of Lemma 6: finite-copy state-conjugation no-go
-- statement:
--   For any d≥2 and any finite k≥0, no fixed two-outcome finite Kraus instrument from k copies of a d-dimensional register to one d-dimensional register has a successful branch sending every normalized pure-state tensor power to p times its entrywise-conjugate pure-state density matrix for one fixed p∈(0,1]. The instrument and p precede the unknown normalized vector. The density matrices are written entrywise, including off-diagonal coherences; k=0 is the scalar empty tensor.
-- source:
--   Universal construction of decoders from encoding black boxes, arXiv:2110.00258v5, PDF p. 20, §4.1 proof of Lemma 6: finite-copy state-conjugation no-go

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P07

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P07

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P06 (Choi)

open QAlgorithms.Papers.Independent.Information100.P34 (choi fromChoi)

open QAlgorithms.Papers.Independent.Claimed50.P48 (FiniteKrausCP)

open QAlgorithms.Papers.Independent.Advance50.P05 (RectangularInstrument)

open QAlgorithms.Papers.Independent.Dependency50.P05 (ChannelChoi)

/-- arXiv:2110.00258v5 PDF pp.19--20, Eq.(51) and its cited state-conjugation
obstruction [80]: no finite-copy physical instrument universally conjugates an
unknown normalized pure state with a nonzero fixed coefficient. The instrument
is chosen before the vector. This is cited background, not a new paper result. -/
theorem finiteCopyConjugation_impossible (d k : ℕ) (hd : 2 ≤ d)
    (A : RectangularInstrument (Word k d) (Fin d) Bool)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ¬ (∀ psi : EuclideanSpace ℂ (Fin d), ‖psi‖ = 1 →
      A.branch false
        (fun u v => ∏ i : Fin k, psi (u i) * conj (psi (v i))) =
          (p : ℂ) • (fun a b => conj (psi a) * psi b)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P07

end
