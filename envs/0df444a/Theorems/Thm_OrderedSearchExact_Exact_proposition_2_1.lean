-- Prove2me | Theorems.Thm_OrderedSearchExact_Exact_proposition_2_1
-- name    : OrderedSearchExact.Exact.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:34.719049+00:00
-- url     : https://prove2.me/theorems/21779ac0-cb6b-42e9-a2eb-d7eda43e8070
-- title:
--   Proposition 2.1 — Laurent characterization in both directions
-- statement:
--   For every $n\ge1$ and $k\ge0$, an exact $k$-query quantum algorithm for $n$-element ordered search exists if and only if a nonnegative real symmetric Laurent path of degree less than $n$ exists with
--
--   $$q_0=F_n,\qquad q_k=1,\qquad\int_0^{2\pi}q_t(e^{i\theta})\,d\theta=2\pi,$$
--   $$J(a^{(t)}-a^{(t-1)})=(-1)^{t+1}(a^{(t)}-a^{(t-1)})\qquad(1\le t\le k).$$
--
--   Normalization is required at every step. The quantum predicate uses actual input-independent unitaries and $k$ calls to the original phase oracle, with success probability one on every transition. The same query count is possible in the symmetrized problem and conversely. The characterization is attributed in the held source to [FGGS99; CCKS26]; it supplies both the forward construction and the unrestricted-query converse.
--
--   Differences from the source:
--   - encoding: normalized real symmetric Laurent polynomials of degree less than n → real coefficient vectors indexed by Fin (n-1), with frequency i+1 and evaluation on every real angle; reason: this bijects the source coefficients, preserves the constant coefficient 1, and includes all points of the unit circle
--   - generalization: the original and symmetrized problems have no query overhead, as stated in the §2.1 preamble → the item also states ExactAlgorithm n k iff SymExactAlgorithm n k; reason: this records the operational bridge on which Proposition 2.1 rests, with the same k and outputs modulo n; it is an added true conjunct, and the first conjunct is the source's iff unchanged, so the item specializes to Proposition 2.1
-- source:
--   Joseph Carolan, Andrew Childs, STOC 2027 submission #1443 (October 2026), Proposition 2.1 [FGGS99; CCKS26]; §2.1, p.6–7 (PDF p.6–7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1443.pdf; sha256 8bb6cbb4037a439039875fd77a9f212e2c0f90a6e87f0c4c690230223813da44

import Definitions.Def_OrderedSearchExact_Exact_Task
import Definitions.Def_OrderedSearchExact_Exact_Laurent

namespace OrderedSearchExact.Exact

theorem proposition_2_1 (n k : ℕ) (hn : 1 ≤ n) :
    (ExactAlgorithm n k ↔ ∃ p : ℕ → Coeff n, FeasiblePath n k p) ∧
      (ExactAlgorithm n k ↔ SymExactAlgorithm n k (by omega)) := by sorry

end OrderedSearchExact.Exact
