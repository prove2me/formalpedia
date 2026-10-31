-- Prove2me | Theorems.Thm_Viterbo_viterbo_of_centrallySymmetric
-- name    : Viterbo.viterbo_of_centrallySymmetric
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T08:18:41.786688+00:00
-- url     : https://prove2.me/theorems/50a0b440-cd55-442a-ac25-e6c9401e621f
-- title:
--   Question 1 — Viterbo's conjecture for centrally symmetric convex domains
-- statement:
--   For every symplectic capacity $c$ on $\mathbb R^{2n}$ and every centrally symmetric convex domain $K \subset \mathbb R^{2n}$ ($z \in K \iff -z \in K$), $c(K)^n \le n!\,\mathrm{Vol}(K)$.
--
--   *Formalization note.* The paper asks this as a question; the statement is its affirmative answer, an open problem.
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. (2) 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), p. 6, Question 1 (open)

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo

open MeasureTheory
open scoped ENNReal

namespace Viterbo

theorem viterbo_of_centrallySymmetric (n : ℕ) (c : Set (OAI.SymmetricPolar.Phase n) → ℝ≥0∞)
    (hc : IsSymplecticCapacity n c) (K : Set (OAI.SymmetricPolar.Phase n)) (hK : IsConvexDomain K)
    (hsymm : ∀ z, z ∈ K ↔ -z ∈ K) :
    c K ^ n ≤ (n.factorial : ℝ≥0∞) * volume K := by
  sorry

end Viterbo
