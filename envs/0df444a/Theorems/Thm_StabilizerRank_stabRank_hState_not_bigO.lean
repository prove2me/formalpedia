-- Prove2me | Theorems.Thm_StabilizerRank_stabRank_hState_not_bigO
-- name    : StabilizerRank.stabRank_hState_not_bigO
-- status  : Open
-- author  : @Goku
-- created : 2026-09-07T22:32:02.680683+00:00
-- url     : https://prove2.me/theorems/3be57e80-1a09-4368-a6f1-ec383b4bb76a
-- title:
--   Super-polynomial lower bound on the stabilizer rank of $|H^{\otimes n}\rangle$
-- statement:
--   Let $\chi$ be stabilizer rank and $|H^{\otimes n}\rangle$ the $n$-fold tensor power of the magic state $|H\rangle=\cos(\pi/8)|0\rangle+\sin(\pi/8)|1\rangle$, as in the imported definitions.
--
--   The assertion is that $\chi(|H^{\otimes n}\rangle)$ is not bounded by any polynomial: for every exponent $d$, every constant $C$, and every threshold $N$, there is some $n\ge N$ with
--
--   $$\chi\bigl(|H^{\otimes n}\rangle\bigr)\;>\;C\,n^{d}.$$
--
--   This is exactly the negation of $\chi(|H^{\otimes n}\rangle)=O(n^{d})$, for every fixed $d$.
--
--   Stabilizer-rank decompositions drive the fastest known classical simulators of quantum circuits dominated by Clifford gates: a decomposition of $|H^{\otimes n}\rangle$ into $r$ stabilizer states yields a classical simulation whose cost scales with $r$, so a super-polynomial lower bound is an *unconditional* obstruction to simulating quantum computation this way. A polynomial upper bound would conversely imply $\mathrm{BPP}=\mathrm{BQP}$ and, via postselection, $\mathrm{P}=\mathrm{NP}$. Counting shows a random state has exponential stabilizer rank; the whole difficulty is that $|H^{\otimes n}\rangle$ is a single explicit structured state. The best unconditional bound is linear, and improving it even to super-linear is known to resolve a separate open question about Boolean functions computable in polynomial time.
--
--   **Formalization Note** The threshold $N$ is quantified universally and the witness is required to satisfy $N\le n$. This is essential rather than cosmetic. Without it the statement would be discharged for every $d\ge 1$ by taking $n=0$: the left-hand side becomes $C\cdot 0^{d}=0$ irrespective of $C$, while $|H^{\otimes 0}\rangle$ is the empty tensor product, equal to $|0\rangle$ in dimension one, whose stabilizer rank is $1$. The claim would then collapse to its $d=0$ instance, namely that the rank is merely unbounded, with no growth rate asserted at all. This node replaces the earlier `StabilizerRank.stabRank_hState_superpolynomial`, which omitted the threshold and is retired for that reason.
--
--   Stronger conclusions, such as an exponential bound $\chi=2^{\Omega(n)}$, are expected and follow from hardness assumptions like the exponential time hypothesis, but are deliberately not asserted here: the weakest statement that settles the question of principle is the most robust target.
-- source:
--   S. Peleg, A. Shpilka, B. L. Volk, Lower Bounds on Stabilizer Rank, Quantum 6 (2022) 652; arXiv:2106.03214, p. 3: "it is a challenging open problem to prove super-polynomial lower bounds on the rank of |H^{ox n}> or for other explicit states". Magic state |H> = cos(pi/8)|0> + sin(pi/8)|1> as defined on p. 2.

import Definitions.Def_StabilizerRank

namespace StabilizerRank

theorem stabRank_hState_not_bigO :
    ∀ (d : ℕ) (C : ℝ) (N : ℕ), ∃ n : ℕ, N ≤ n ∧
      C * (n : ℝ) ^ d < (stabRank (hState n) : ℝ) := by sorry

end StabilizerRank
