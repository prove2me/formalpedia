-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P80_bb84_trajectory_invariants
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P80.bb84_trajectory_invariants
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:58:32.729076+00:00
-- url     : https://prove2.me/theorems/8eb6a209-163b-46ad-a511-5cabd25f4dac
-- title:
--   BB84 purification trajectories preserve the two Claim 10 inequalities
-- statement:
--   Let $0\le p<1/4$ and $0\le a\le p$. Start with independent Pauli noise $(q_X,q_Y,q_Z)=(p-a,a,p-a)$. Fix any finite word of B and P steps whose first step is B; its suffix may be empty. For each prefix, compute the conditional Pauli error rates by performing those steps, and write $p_Z=q_X+q_Y$ and $\Delta=q_Z-q_Y$ for the resulting bit-error probability and error difference. Index prefixes by $j$, with $j=0$ denoting the initial distribution. Then
--
--   $$
--   \Delta_j\ge0\quad(1\le j\le L),\qquad
--   1-2p_{Z,j}-2\Delta_j>0\quad(0\le j\le L),
--   $$
--
--   where $L$ is the length of the fixed word. Thus the first inequality begins after the initial B step, while the second also holds before purification.
--
--   These are invariants of the computed BB84 trajectories used in the worst-channel argument; they impose no invariant hypotheses on arbitrary error triples.
-- source:
--   Proof of security of quantum key distribution with two-way classical communications, arXiv:quant-ph/0105121v2, PDF p. 23, Claim 10, with Theorem 9 assumptions on p.22

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P80

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P80

open scoped ComplexConjugate

/-- Claim 10, PDF p.23, inheriting Theorem 9's setup on p.22.
The strict inequality holds initially and at every prefix. Delta need only
be nonnegative after the mandatory first B. The suffix is any fixed finite
B/P word, including the empty word; trajectories are computed, not supplied
as arbitrary triples satisfying invariant hypotheses. -/
theorem bb84_trajectory_invariants (p a : ℝ)
    (hp : 0 ≤ p) (hpUpper : p < 1 / 4) (ha : 0 ≤ a) (haUpper : a ≤ p)
    (suffix : List PurificationStep) :
    0 < 1 - 2 * bitError (bb84Rates p a) - 2 * pauliErrorDifference (bb84Rates p a) ∧
    ∀ k : ℕ, k ≤ suffix.length →
      let q := runSteps (.B :: suffix.take k) (bb84Rates p a)
      0 ≤ pauliErrorDifference q ∧ 0 < 1 - 2 * bitError q - 2 * pauliErrorDifference q := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P80

end
