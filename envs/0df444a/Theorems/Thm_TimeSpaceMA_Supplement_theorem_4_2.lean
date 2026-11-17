-- Prove2me | Theorems.Thm_TimeSpaceMA_Supplement_theorem_4_2
-- name    : TimeSpaceMA.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:46:20.919104+00:00
-- url     : https://prove2.me/theorems/05b1d01f-ef72-4ac2-b5a0-e68bb8cae9ab
-- title:
--   Theorem 4.2 — $\mathrm{MATIME}[n]\not\subseteq\mathrm{DTISP}[n^{2+\delta},n^\delta]$ for some $\delta>0$
-- statement:
--   There is a fixed constant $\delta>0$ and a language $L$ with a linear-cost Merlin–Arthur protocol such that no deterministic random-access-input machine decides $L$ simultaneously in time $O(n^{2+\delta})$ and space $O(n^\delta)$:
--
--   $$
--   \mathrm{MATIME}[n]\not\subseteq\mathrm{DTISP}[n^{2+\delta},n^\delta].
--   $$
--
--   The same constant $\delta$ appears in the superquadratic time exponent and the positive space exponent. This is the paper's first superquadratic time–space lower bound for classical linear-time Merlin–Arthur protocols.
--
--   **Formalization Note** `InMATIME` includes perfect completeness and soundness $1/3$ and measures message length plus the work of a uniform log-cost RAM verifier. `InDTISP` is the published deterministic random-access-input class.
--
--   Differences from the source:
--   - reading: the displayed theorem says problems with n·poly(log n)-time MA protocols → the stronger statement immediately below it, MATIME[n] ⊈ DTISP[n^{2+δ},n^δ]; reason: the paper explicitly says this is what it proves, and it implies the displayed wording
--   - encoding: asymptotic real powers n^{2+δ} and n^δ → one positive uniform multiplier times ceilings of max{n,1}^{2+δ} and max{n,1}^δ; reason: the multiplier encodes the hidden big-O constants, natural ceilings make the budgets discrete, and max{n,1} removes only the zero-length boundary
--   - encoding: algorithms and MA protocols with no fixed machine syntax → the published TimeSpaceMA.RATM for DTISP and finite programs of the published log-cost RAM for MATIME; reason: these are the machine conventions already used by the paper's published base mission
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), Theorem 4.2 (Theorem 1.2, restated) and the following stronger statement, p.24; proof pp.25–29 and Appendix A.7, pp.38–39

import Definitions.Def_TimeSpaceMA_InDTISP
import Definitions.Def_TimeSpaceMA_Supplement_InMATIME

set_option autoImplicit false

namespace TimeSpaceMA
namespace Supplement

/-- **Theorem 4.2 (Theorem 1.2, restated)** (Williams–Xi, *Short Non-Interactive Proofs for
Time-Space Computations*, STOC 2027 submission, manuscript sha256 184c2f95…, p.24).
There is one fixed `δ > 0` and one language in `MATIME[n]` that is not decidable simultaneously
in deterministic time `n^(2+δ)` and space `n^δ`.

**Formalization Note** This is the stronger precise statement immediately following the printed
wording on p.24, `MATIME[n] ⊈ DTISP[n^(2+δ), n^δ]`. The same existential `δ` occurs in
both exponents, before the hard language. The positive constant `C` inside the negation is the
uniform multiplicative constant hidden by the asymptotic `DTISP` notation; one common constant is
equivalent to separate time and space constants by taking their maximum. Real powers are rounded up,
and `max n 1` removes only the undefined asymptotic boundary at input length zero. `InDTISP` is the
published deterministic random-access-input class; `InMATIME` is the uniform log-cost RAM protocol
class with perfect completeness and soundness `1/3`. -/
theorem theorem_4_2 : ∃ δ : ℝ, 0 < δ ∧ ∃ L : Set (List Bool),
    InMATIME L (fun n => n) ∧
      ¬ ∃ C : ℕ, 0 < C ∧
        InDTISP L
          (fun n => C * Nat.ceil ((max (n : ℝ) 1) ^ (2 + δ)))
          (fun n => C * Nat.ceil ((max (n : ℝ) 1) ^ δ)) := by sorry

end Supplement
end TimeSpaceMA
