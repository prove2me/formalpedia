-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_5_1
-- name    : TreeEquivalenceHORS.Equivalence.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:59.922233+00:00
-- url     : https://prove2.me/theorems/cf0078d2-8c50-4c2e-becc-e8dce6906377
-- title:
--   Lemma 5.1 (Syntactic compilation): $G^\diamond_M$ is a well-formed scheme over $\Sigma_0$ of order at most four
-- statement:
--   For every two-counter program $M$ and side $\diamond\in\{L,R\}$, the compiled scheme $G^\diamond_M$ of Figure 3 is a finite, closed, well-typed deterministic HORS over $\Sigma_0=\{z:0,a:1,b:3\}$, and
--   $$\operatorname{ord}(G^\diamond_M)\le4.$$
--
--   This is the static half of the intermediate compilation theorem.
--
--   Differences from the source:
--   - encoding: finite, closed, well-typed deterministic HORS → `Valid` (one rule per nonterminal, start of type o, every body of type o with only declared references); finiteness and determinism hold for every `HORS` value; reason: finite lists encode the declarations and rule bodies; `Valid` enforces exactly one well-typed body per declared nonterminal
--   - encoding: Σ₀ = {z:0, a:1, b:3}, Σ₂ = {e:0, d:2} → `sigma0 = [0, 1, 3]` (terminals 0 = z, 1 = a, 2 = b) and `sigma2 = [0, 2]` (0 = e, 1 = d); reason: a ranked alphabet is its list of arities, terminals named by position
-- source:
--   Mingkun Xiao, Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, STOC 2027 submission #421 (October 2026), source.pdf SHA-256 e875d09ced029e3f5cb114abba049e4a2b1bdaa9b064c98b0d71f2ec7451c7af, Lemma 5.1, printed p. 16 / PDF p. 18

import Mathlib
import Definitions.Def_TreeEquivalenceHORS_Equivalence_Compiler

namespace TreeEquivalenceHORS.Equivalence

/-- **Lemma 5.1 (Syntactic compilation)** (printed p. 16 / PDF p. 18). For every source program `M`
and side `⋄`, the compiled scheme `G^⋄_M` is a well-formed (finite, closed, well-typed,
deterministic) scheme over `Σ₀` of order at most four. -/
theorem lemma_5_1 (M : Machine) (side : Side) :
    (compile side M).Valid ∧ (compile side M).alphabet = sigma0 ∧ (compile side M).order ≤ 4 := by sorry

end TreeEquivalenceHORS.Equivalence
