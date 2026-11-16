-- Prove2me | Theorems.Thm_PooledTestingAdaptivity_Gap_Supplement_theorem_3_9
-- name    : PooledTestingAdaptivity.Gap.Supplement.theorem_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:40:14.773313+00:00
-- url     : https://prove2.me/theorems/b64ecfdf-b5ec-4160-880e-b24082afcace
-- title:
--   Theorem 3.9 — Deciding $\mathrm{OPT}_{\mathrm{dyn}}(B,J)\ge\tau$ is NP-hard for every fixed pool cap $G\ge3$
-- statement:
--   For every fixed natural number $G\ge3$, the following decision problem is NP-hard under polynomial-time many-one reductions: given a standard-model instance $J$ with $n\ge1$ individuals, positive rational health probabilities $0<q_i\le1$, nonnegative integer utilities $u_i$ and pool cap $G$, a budget $B$ and a rational threshold $\tau$, decide whether
--   $$\mathrm{OPT}_{\mathrm{dyn}}(B,J)\ge\tau .$$
--
--   Fixing the pool cap makes static greedy approximation polynomial, but it does not make exact dynamic optimization tractable unless $\mathrm P=\mathrm{NP}$. Only hardness is asserted; membership in NP is not claimed.
--
--   Differences from the source:
--   - encoding: the input (J, B, τ) → the binary string over {0, 1, sep, #} of n, the q_i and τ as reduced rationals, the u_i and B as naturals; reason: standard binary encoding, the input-size convention of the source
--   - encoding: NP-hard → KingTerrain.NPHard.IsNPHard over CookPvsNP languages (every NP language over a finite alphabet reduces in polynomial time); reason: the standard definition
-- source:
--   Edwin Lock, Nicholas Lopez, Francisco Marmolejo-Cossío, Jose Roberto Tello Ayala, David Parkes, STOC 2027 submission #1397 (October 2026), Theorem 3.9, printed p. 11, PDF p. 12; proof §8.1, printed p. 26, PDF p. 27

import Mathlib
import Definitions.Def_KingTerrain_NPHard_Complexity
import Definitions.Def_PooledTestingAdaptivity_Gap_Supplement_Hardness

namespace PooledTestingAdaptivity.Gap.Supplement

/-- Theorem 3.9 (Hardness for a fixed pool cap), printed p. 11, PDF p. 12; proof §8.1,
printed p. 26. For every fixed `G ≥ 3`, deciding `OPT_dyn(B,J) ≥ τ` is NP-hard. -/
theorem theorem_3_9 (G : ℕ) (hG : 3 ≤ G) :
    KingTerrain.NPHard.IsNPHard (DynOptLang G) := by sorry

end PooledTestingAdaptivity.Gap.Supplement
