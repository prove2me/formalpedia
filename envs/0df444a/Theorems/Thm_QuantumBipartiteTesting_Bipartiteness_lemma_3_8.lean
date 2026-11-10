-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_3_8
-- name    : QuantumBipartiteTesting.Bipartiteness.lemma_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:13:14.493204+00:00
-- url     : https://prove2.me/theorems/344b980b-6923-4637-96e0-4ec05730cae0
-- title:
--   Lemma 3.8 — full cycle-rank divisibility
-- statement:
--   There is a positive absolute degree constant such that, for every consistent three-colored pattern $F$ with at most $2q$ edges, there is a real bivariate polynomial $B_F$ of degree $O(q\log q)$ satisfying
--   $$W_F(M,\ell)=\frac{\ell^{\beta(F)}B_F(M,\ell)}{D_q(M,\ell)},\qquad\beta(F)=e(F)-v(F)+c(F).$$
--   The equality is an identity away from $\ell=0$ and the poles of $D_q$. The full integer cycle-rank exponent is retained, including patterns with differently colored parallel edges and the empty pattern. This is the divisibility statement used to isolate a factor of $\ell$ in the formal gap.
--
--   Differences from the source:
--   - encoding: vertices [N], distinct undirected edges and color-labeled parallel edges → Fin N; oriented unordered pairs; color included in each edge identifier; reason: bijections relabel vertices; differently colored parallel constraints remain distinct
--   - encoding: degree O(q log q) → a positive universal multiple of 1 + q log(q+2); reason: the two rates agree as q tends to infinity; the globally defined expression also retains q=0 and q=1 without artificial hypotheses
--   - reading: formal expectation described both by (A.2)–(A.4) and by arbitrary output on overflow → the algebraic partition functional (A.2)–(A.4), followed by signing probabilities and linear extension; reason: these descriptions disagree at N=M=4,l=2: a one-edge moment is 1/2 algebraically versus 1/8 with empty output on overflow; the feasible law stays conditional and its comparison remains a theorem
--   - reading: Definition 3.6 gives structural matching/response consistency and calls it equivalent to positive sampling probability → consistency is the structural condition, without a parameter-dependent positivity certificate; reason: a three-vertex two-color path is structurally consistent but cannot fit any block when N=M=4,l=2; retaining the structural definition preserves the full algebraic pattern domain
--   - encoding: identities of rational functions → real evaluations with l nonzero and D_q nonzero; grid nonvanishing is concluded eventually in the small-query range; reason: division at a pole is undefined in the source; Lean totalized division is never used to certify an identity there
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), Lemma 3.8, PDF = printed page 16. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction

namespace QuantumBipartiteTesting.Bipartiteness
open Finset

theorem lemma_3_8 : ∃ Cdeg : ℝ, 0 < Cdeg ∧
    ∀ N q : ℕ, ∀ F : Finset (ColoredEdge N), Consistent F → F.card ≤ 2*q →
    ∃ B : Bivariate, (B.totalDegree : ℝ) ≤ Cdeg * DegreeScale q ∧
      ∀ M l : ℝ, l ≠ 0 → Eval (Denominator q) M l ≠ 0 →
        TopologyMoment F M l = l ^ CycleRank F * Eval B M l / Eval (Denominator q) M l := by sorry

end QuantumBipartiteTesting.Bipartiteness
