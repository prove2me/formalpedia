-- Prove2me | Theorems.Thm_SublinearChoresMMS_Disposal_lemma_a_2
-- name    : SublinearChoresMMS.Disposal.lemma_a_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T03:31:53.622445+00:00
-- url     : https://prove2.me/theorems/e43edf4e-bf27-4f60-bf71-89f769fe9d8d
-- title:
--   Lemma A.2 — retaining half the copies with paired-capacity loads
-- statement:
--   There are absolute constants $C_3>5$ and $b_0\ge2$ such that the following holds in the normalized ordered regime. Put $q=2^\ell$, take $0\le j<\ell$, and assume the padded stage has an even number $b\ge b_0$ of bins as prescribed in Appendix A.1.2. Each representative except the first has $q/2^j$ copies. Their old marked set has size $M_j\le8C_3\sqrt{n/2^j}$; every bin's unmarked load is feasible and every zero-capacity padding bin is empty.
--
--   There exist a retained set containing exactly half the copies of each representative, a marked subset of the retained copies containing every retained old mark, and a pairing preserving the exceptional pair, such that every merged pair satisfies
--
--   $$\text{retained unmarked load}(u,v)\le\frac{T_u+T_v}{2},\qquad M_{j+1}\le\frac{M_j}{2}+C_3\sqrt b.$$
--
--   The mark count includes retained old marks and new marks. All choices, including the pairing and new marks, are conclusions.
--
--   Differences from the source:
--   - generalization: the power of two q fixed in Section 3 → any q=2^ell with j<ell, divisibility, the invariant, and sufficiently many stage bins; reason: the local halving argument uses only the even representative multiplicities, current capacities, and feasible effective costs; the prescribed q is included
--   - encoding: an arbitrary selected unit bin in the odd-unit case → the selected unit bin is labelled zero; reason: unit bins can be relabelled without changing any copy, cost, or feasibility condition
--   - encoding: finite agents, chores, complete partitions and finite lotteries → agents Fin n, chores Fin m, allocation maps and normalized finite lists with real weights; reason: bijections identify the same finite instances and partitions; repeated lottery atoms may be merged and positive weights define support
--   - encoding: cost minimax share over labelled partitions → the negative of LittleCharity.MMS.mms evaluated at negative additive bundle costs; reason: negation exchanges finite maxima and minima; no goods nonnegativity predicate is imposed, and costShare_spec states the attained minimax characterization
-- source:
--   Zehan Lin, Xiaowei Wu, Shengwei Zhou, STOC 2027 submission #845 (October 2026), Lemma A.2 with Invariant A.1 and Appendix A.1.2, printed pp. 20–24 / PDF pp. 21–25; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/845.pdf

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Packing

noncomputable section

namespace SublinearChoresMMS.Disposal

/-- Lemma A.2 with the complete Invariant A.1 context, printed pp. 20–21 / PDF pp. 21–22.
The absolute constant and sufficiently large bin threshold precede all packing data. -/
theorem lemma_a_2 :
    ∃ C₃ : ℝ, 5 < C₃ ∧ ∃ b₀ : ℕ, 2 ≤ b₀ ∧
      ∀ (n m ℓ j : ℕ), j < ℓ → 0 < n → 0 < m →
        2 ^ ℓ ∣ m → b₀ ≤ stageBins n j →
        ∀ (c : Cost n m), Normalized c → ∀ (i : Fin n)
          (P : CopyPacking n m (2 ^ ℓ) j),
          CopyFeasible c i P →
          (P.marked.card : ℝ) ≤ 8 * C₃ * Real.sqrt ((n : ℝ) / ((2 ^ j : ℕ) : ℝ)) →
          HalvingOutput c i P C₃ := by sorry

end SublinearChoresMMS.Disposal
