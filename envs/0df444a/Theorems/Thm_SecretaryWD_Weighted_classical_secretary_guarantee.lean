-- Prove2me | Theorems.Thm_SecretaryWD_Weighted_classical_secretary_guarantee
-- name    : SecretaryWD.Weighted.classical_secretary_guarantee
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:26:29.304986+00:00
-- url     : https://prove2.me/theorems/87dc5e7b-ac11-4f55-a726-fa94332b18fc
-- title:
--   Section 2 — the classical secretary rule succeeds with probability at least $1/e$
-- statement:
--   Let $n\ge1$ agents of nonnegative value arrive in a uniformly random order. Observe the first $\lfloor n/e\rfloor$ without selecting anyone, then select the first agent who outranks every earlier arrival. With a fixed tie break, this rule selects the maximum-valued agent with probability at least $1/e$:
--
--   $$\Pr(e_{\mathrm{sec}}=e_{\max})\ge\frac1e.$$
--
--   This is the classical guarantee used for the single large-value case of Theorem 3.4.
--
--   **Formalization Note** Equal values are resolved by smaller original agent index, so the event concerns a unique maximum. The probability is a finite average over all $n!$ permutations.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 4, Section 2, classical secretary algorithm

import Mathlib
import Definitions.Def_SecretaryWD_Weighted_Assignment
import Definitions.Def_SecretaryWD_Weighted_ReservationAlgorithm

namespace SecretaryWD.Weighted

/-- Section 2: the `⌊n/e⌋` observation rule selects the maximum with probability at least `1/e`. -/
theorem classical_secretary_guarantee {n : ℕ} (hn : 0 < n)
    (v : Fin n → ℝ) (hv : ∀ e, 0 ≤ v e) :
    1 / Real.exp 1 ≤
      orderAverage (fun π =>
        if ∃ t : Fin n,
            classicalSecretary n (fun s => (v (π s), π s)) = some t ∧
              valueRank v (π t) = 0 then (1 : ℝ) else 0) := by sorry

end SecretaryWD.Weighted
