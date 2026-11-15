-- Prove2me | Theorems.Thm_SymmetricPSM1041_ORLowerBound_Supplement_no_consistent_coloring_obstruction
-- name    : SymmetricPSM1041.ORLowerBound.Supplement.no_consistent_coloring_obstruction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:50:06.183022+00:00
-- url     : https://prove2.me/theorems/d7a35e1a-90b1-4531-98db-30416ce51583
-- title:
--   Theorem 28 — no consistent coloring family, no $(n,K)$-protocol
-- statement:
--   Let $f:\{0,1\}^n\to\{0,1\}$, let $K$ be a positive integer and $b\in\{0,1\}$. Suppose there is no $b$-consistent $K$-coloring family for $f$. Then no PSM protocol $P$ for $f$ all of whose local alphabets have at most $K$ messages,
--
--   $$|\mathcal A_i(P)|\le K\quad\text{for all }i\in[n],$$
--
--   is both perfectly correct and support private. Here $\mathcal A_i(P)$ is the set of messages party $i$ actually sends.
--
--   This is the general form of the paper's cube-system lower bound: an alphabet lower bound for $f$ follows from a purely combinatorial nonexistence statement about colorings.
--
--   Differences from the source:
--   - encoding: parties indexed by [n]={1,…,n} → parties indexed by Fin n; reason: the bijection i↦i+1 preserves every input and coordinate subset
--   - encoding: arbitrary finite nonempty shared seed set R → Fin P.seedCount with positive unrestricted seedCount; reason: reindexing preserves uniform laws, supports and realized lengths
--   - encoding: (n,K)-protocol: declared local alphabets of size at most K → actual message-image alphabets of size at most K; reason: unused symbols can be removed and the decoder restricted, preserving correctness, support privacy and transcript lengths
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), p. 19, Definition (Consistent Coloring Family) and Theorem 28 (proof p. 19)

import Mathlib
import Definitions.Def_SymmetricPSM1041_ORLowerBound_CostsRestrictions
import Definitions.Def_SymmetricPSM1041_ORLowerBound_Supplement_ColoringsSubfunctions

namespace SymmetricPSM1041.ORLowerBound.Supplement

theorem no_consistent_coloring_obstruction {n : ℕ} (f : (Fin n → Bool) → Bool)
    (K : ℕ) (hK : 0 < K) (b : Bool)
    (hno : ¬ ∃ α : (Fin n → Bool) → Fin n → Fin K, IsConsistentColoringFamily f K b α) :
    ∀ P : PSM (Fin n), (∀ i, (localAlphabet P i).card ≤ K) →
      ¬ (PerfectCorrect P f ∧ SupportPrivate P f) := by sorry

end SymmetricPSM1041.ORLowerBound.Supplement
