-- Prove2me | Theorems.Thm_Turing_TM2ComputableInPolyTime_comp_of_polytime
-- name    : Turing.TM2ComputableInPolyTime.comp_of_polytime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T03:46:43.177987+00:00
-- url     : https://prove2.me/theorems/5b3ff7b0-a6cd-4c33-b40a-6fd6334ba249
-- title:
--   Polynomial-time Turing machine computability is closed under composition (Mathlib `proof_wanted`)
-- statement:
--   Closure of polynomial-time computability of multi-tape Turing machines under composition.
--
--   Let $\alpha, \beta, \gamma$ be encodable types with encodings $e_\alpha, e_\beta, e_\gamma$ into lists, and let $f : \alpha \to \beta$, $g : \beta \to \gamma$ be computed by polynomial-time multi-tape Turing machines (in Mathlib's `TM2` model, where the running time is a polynomial in the input length). Then the composite $g \circ f$ is also computed by a polynomial-time machine:
--
--   $$\exists\, M,\quad M \text{ computes } g\circ f \text{ in time } p(n) + q\bigl(2\,s_1(n) + 1\bigr) + O\bigl(s_1(n)\bigr),$$
--
--   where $p$ bounds the first machine, $q$ the second, and $s_1(n) = n + p(n)\cdot\mathrm{growth}_1$ bounds the intermediate output length.
--
--   This is the statement of Mathlib's `proof_wanted Turing.TM2ComputableInPolyTime.comp` (`Mathlib/Computability/TuringMachine/Computable.lean`), which had no proof in the library. The construction runs the first machine, copies its output stack onto the second machine's input stack by two LIFO passes through the machines' alphabet equivalences (one symbol per step), then runs the second machine; the time bound combines the two polynomials with the intermediate-length growth estimate.
--
--   **Formalization Note.** No hypothesis is imposed on the intermediate alphabet $\beta_\Gamma$: the inhabited case is handled by the two-pass copy, and the empty case by a jump (the second machine must then ignore its input, since the intermediate encoding is empty).
-- source:
--   Mathlib4, Mathlib/Computability/TuringMachine/Computable.lean, `proof_wanted TM2ComputableInPolyTime.comp` (statement verbatim; proof absent in the library); standard multi-tape Turing machine composition

import Mathlib

theorem Turing.TM2ComputableInPolyTime.comp_of_polytime
    {α β γ αΓ βΓ γΓ : Type} {eα : α → List αΓ} {eβ : β → List βΓ} {eγ : γ → List γΓ}
    {f : α → β} {g : β → γ}
    (h1 : Turing.TM2ComputableInPolyTime eα eβ f) (h2 : Turing.TM2ComputableInPolyTime eβ eγ g) :
    Nonempty (Turing.TM2ComputableInPolyTime eα eγ (g ∘ f)) := by sorry
