-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P07_choi_backgroundCharacterization
-- name    : QAlgorithms.Papers.Independent.Extend50.P07.choi_backgroundCharacterization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:50:50.217188+00:00
-- url     : https://prove2.me/theorems/d7a8a2f4-fa36-48b8-b9a5-d982ae37a7ba
-- title:
--   Appendix A: Choi, composition and one-slot superinstrument characterization
-- statement:
--   For positive finite dimensions, an unnormalized input-first Choi matrix J represents a completely positive map exactly when J is positive semidefinite, and a channel exactly when its output partial trace is the identity. Composition contracts the intermediate input/output indices. For two linear one-slot Choi supermaps S,T, being the branches of a General instrument is equivalent to positive Choi operators and the affine partial-trace conditions (76)-(78). The first condition removes dependence on the oracle output after tracing the future; the second full slot/future trace is D times the identity on the past. All operator identities are on arbitrary matrices, with no normalization of the Choi matrix by the input dimension.
-- source:
--   Universal construction of decoders from encoding black boxes, arXiv:2110.00258v5, PDF p. 28, Appendix A: Choi, composition and one-slot superinstrument characterization

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

/-- arXiv:2110.00258v5 PDF pp.27--28, Appendix A, Eqs.(70)--(79):
unnormalized Choi CP/TP characterization, composition, and the complete physical
one-slot instrument characterization. This is cited background, not a new result
of Yoshida--Soeda--Murao. The two finite normalizations retain all four wires. -/
theorem choi_backgroundCharacterization (d D P F : ℕ)
    (hd : 0 < d) (hD : 0 < D) (hP : 0 < P) (hF : 0 < F) :
    (∀ J : Choi (Fin d) (Fin D),
      (FiniteKrausCP (fromChoi J) ↔ J.PosSemidef) ∧
      (IsChannel (fromChoi J) ↔ ChannelChoi J)) ∧
    (∀ J : Choi (Fin d) (Fin D), ∀ K : Choi (Fin D) (Fin F),
      choi (fun X => fromChoi K (fromChoi J X)) =
        (fun a b => ∑ o : Fin D, ∑ q : Fin D,
          J (a.1, o) (b.1, q) * K (o, a.2) (q, b.2))) ∧
    (∀ S T : Choi (Word 1 d) (Word 1 D) →ₗ[ℂ] Choi (Fin P) (Fin F),
      (∃ A : General d D P F 1, A.success = S ∧ A.failure = T) ↔
      (choi S).PosSemidef ∧ (choi T).PosSemidef ∧
      (let C := choi S + choi T
       (∀ u v : Word 1 d, ∀ o q : Word 1 D, ∀ x y : Fin P,
         (∑ f : Fin F, C ((u, o), (x, f)) ((v, q), (y, f))) =
           ((if o = q then (1 : ℂ) else 0) / (D : ℂ)) *
             ∑ r : Word 1 D, ∑ f : Fin F,
               C ((u, r), (x, f)) ((v, r), (y, f))) ∧
       (∀ x y : Fin P,
         (∑ u : Word 1 d, ∑ o : Word 1 D, ∑ f : Fin F,
           C ((u, o), (x, f)) ((u, o), (y, f))) =
             (D : ℂ) * (if x = y then 1 else 0)))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P07

end
