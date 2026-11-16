-- Prove2me | Theorems.Thm_SuperRamanujan227_Main_Supplement_theorem_4_5
-- name    : SuperRamanujan227.Main.Supplement.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:47:56.700212+00:00
-- url     : https://prove2.me/theorems/fc7f416c-4462-480b-9bad-6996722c45f2
-- title:
--   Theorem 4.5 — Exact rational-square threshold search
-- statement:
--   There is one deterministic algorithm and constants $C>0$, $k\in\mathbb N$ with the following guarantee. Let $n$ be even, $3\le d\le n/2$, and let $s>0$ be rational. Write $L(s)$ for the total binary length of its reduced numerator and denominator, $b=\sqrt{s}$, and $p_\varnothing$ for the actual $(n,d)$-root characteristic polynomial of Definition 4.4. If
--
--   $$\alpha_2(p_\varnothing)\le b,$$
--
--   then the algorithm outputs a $d$-regular bipartite multigraph $G$ on $n$ vertices with
--
--   $$\lambda(G)\le b,$$
--
--   in at most $C(n+L(s)+1)^k$ machine steps. Consequently every polynomial bound on the bit length gives the printed polynomial-in-$n$ guarantee, without selecting a fixed bit-budget exponent. The hypothesis concerns the second root of the averaged characteristic polynomial including both trivial roots. The threshold remains arbitrary; it is not restricted to the value used for Theorem 4.1. The exact-arithmetic discussion on p.14 supplies uniform dependence on threshold length.
--
--   Differences from the source:
--   - encoding: n=2m and admissible degree d≤m in the surrounding construction setting → even n and 3≤d≤n/2 in the theorem binders; reason: the lower degree bound and construction context are inherited from §4, rather than added spectral assumptions
--   - encoding: positive rational threshold of polynomial bit complexity and time poly(n) → one finite binary machine with time C(n+L(s)+1)^k for all positive rational s; reason: uniform exact arithmetic in Q[√s] on p.14 gives polynomial dependence on threshold length, hence the printed guarantee for every polynomial bit budget
--   - encoding: the largest absolute nontrivial eigenvalue → maximum after deleting one top eigenvalue and, for a bipartite graph, one bottom eigenvalue, with multiplicity; reason: this removes the canonical trivial directions and retains extra copies in disconnected graphs
-- source:
--   Gil Cohen, Gal Maor, STOC 2027 submission #227 (October 2026), p. 14, Theorem 4.5

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_Supplement_Spectral
import Definitions.Def_SuperRamanujan227_Main_Supplement_Computation
import Definitions.Def_SuperRamanujan227_Main_Supplement_RootPolynomial

namespace SuperRamanujan227.Main.Supplement

/-- Theorem 4.5, p.14: one exact binary machine, uniformly polynomial in n plus the bit
length of s. This gives poly(n) for every polynomial bit budget, with no fixed budget exponent. -/
theorem theorem_4_5 :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C k : ℕ), 0 < C ∧
      ∀ (n d : ℕ) (s : ℚ), Even n → 3 ≤ d → d ≤ n / 2 → 0 < s →
        kthLargestRoot (rootCharacteristic n d) 2 ≤ Real.sqrt (s : ℝ) →
        ∃ G : Multigraph n, G.IsRegular d ∧ MatrixBipartite G.adj ∧
          spectralRadius G ≤ Real.sqrt (s : ℝ) ∧
          Runs M (thresholdInput n d s) (graphOutput G)
            (C * (n + rationalBits s + 1)^k) := by sorry

end SuperRamanujan227.Main.Supplement
