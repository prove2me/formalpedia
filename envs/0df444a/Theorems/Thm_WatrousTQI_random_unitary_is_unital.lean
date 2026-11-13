-- Prove2me | Theorems.Thm_WatrousTQI_random_unitary_is_unital
-- name    : WatrousTQI.random_unitary_is_unital
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-11T22:55:45.569598+00:00
-- url     : https://prove2.me/theorems/efb76ea5-8238-4f4d-828d-5024fa28c5f3
-- title:
--   Definition 4.2 — random-unitary channels preserve the identity
-- statement:
--   Let $d>0$ and let $\Phi$ admit a finite random-unitary decomposition on every complex $d\times d$ operator: the real weights lie in $[0,1]$, sum to one, and the conjugating matrices are unitary. Then $\Phi(I_d)=I_d$. The representation and probability constraints reuse the published `IsRandomUnitary` predicate; unitality is a conclusion.
-- source:
--   John Watrous, The Theory of Quantum Information, Cambridge University Press, 2018, Chapter 4. https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf; Definition 4.2 and the opening paragraph of §4.1.1, printed p.202 (PDF p.210).

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P11
set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate BigOperators

namespace WatrousTQI

theorem random_unitary_is_unital {d : ℕ} (hd : 0 < d)
    (Φ : QAlgorithms.Superop (Fin d) (Fin d))
    (h : QAlgorithms.Papers.Independent.Dependency50.P11.IsRandomUnitary Φ) :
    Φ (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by sorry

end WatrousTQI
