-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_proposition_3_10
-- name    : QuantumBipartiteTesting.Bipartiteness.proposition_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:13:05.050231+00:00
-- url     : https://prove2.me/theorems/c13eb8a7-cb3b-4a19-9ede-2b400434bacd
-- title:
--   Proposition 3.10 — formal gap numerator factor
-- statement:
--   For every actual $q$-query signed-graph circuit, there is a real bivariate polynomial $H$, with a universal $O(q\log q)$ degree bound, such that
--   $$\Delta^{\rm form}(M,\ell)=\frac{\ell H(M,\ell)}{D_q(M,\ell)}.$$
--   The equality holds for every real parameter pair away from $\ell=0$ and the denominator poles. All circuit data are fixed before the parameter pair, and the formal gap is computed from the explicit canonical polynomial and partition functional. This states the factorization as a conclusion rather than a supplied hardness certificate.
--
--   Differences from the source:
--   - encoding: finite quantum query circuits with binary encoded outcomes and arbitrary workspace → published QueryAlg, arbitrary finite complex registers, injective null-zero bit encoding, unitary XOR oracle, input-independent output event; reason: every finite workspace is represented up to a basis bijection; unused answer bit strings and dummy vertex queries are retained
--   - encoding: degree O(q log q) → a positive universal multiple of 1 + q log(q+2); reason: the two rates agree as q tends to infinity; the globally defined expression also retains q=0 and q=1 without artificial hypotheses
--   - reading: formal expectation described both by (A.2)–(A.4) and by arbitrary output on overflow → the algebraic partition functional (A.2)–(A.4), followed by signing probabilities and linear extension; reason: these descriptions disagree at N=M=4,l=2: a one-edge moment is 1/2 algebraically versus 1/8 with empty output on overflow; the feasible law stays conditional and its comparison remains a theorem
--   - reading: Definition 3.6 gives structural matching/response consistency and calls it equivalent to positive sampling probability → consistency is the structural condition, without a parameter-dependent positivity certificate; reason: a three-vertex two-color path is structurally consistent but cannot fit any block when N=M=4,l=2; retaining the structural definition preserves the full algebraic pattern domain
--   - encoding: identities of rational functions → real evaluations with l nonzero and D_q nonzero; grid nonvanishing is concluded eventually in the small-query range; reason: division at a pole is undefined in the source; Lean totalized division is never used to certify an identity there
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), Proposition 3.10, PDF = printed page 16. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction

namespace QuantumBipartiteTesting.Bipartiteness
open Finset

theorem proposition_3_10 : ∃ Cdeg : ℝ, 0 < Cdeg ∧
    ∀ N k w q : ℕ, ∀ E : Encoding (Fin N × Bool) k,
    ∀ A : Algorithm (Address N 3) k w q,
    ∀ out : (Address N 3 × Bits k) × Fin w → Bool,
    ∃ H : Bivariate, (H.totalDegree : ℝ) ≤ Cdeg * DegreeScale q ∧
      ∀ M l : ℝ, l ≠ 0 → Eval (Denominator q) M l ≠ 0 →
        FormalGap E A out M l = l * Eval H M l / Eval (Denominator q) M l := by sorry

end QuantumBipartiteTesting.Bipartiteness
