-- Prove2me | Theorems.Thm_TwoMasterRoommates_Capped_Supplement_theorem_D_6
-- name    : TwoMasterRoommates.Capped.Supplement.theorem_D_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:37:11.933235+00:00
-- url     : https://prove2.me/theorems/d95c5488-7053-4912-8419-9617c96d7987
-- title:
--   Theorem D.6 (= Theorem 1.3) — no deterministic PTAS unless P = NP
-- statement:
--   Consider the preference domain of Theorem D.1 with rewards in the fixed nonnegative alphabet $\{0,21,22,23,31\}$, restricted to instances that have a weakly stable perfect matching. Suppose that for every rational $\varepsilon>0$ there is a deterministic polynomial-time algorithm that, on every such instance, returns a weakly stable perfect matching $M$ with
--
--   $$w(M)\ge(1-\varepsilon)\,\mathrm{OPT},$$
--
--   where $\mathrm{OPT}$ is the maximum reward of a weakly stable perfect matching. Then $\mathrm{P}=\mathrm{NP}$: every NP language over every finite alphabet is in P.
--
--   Together with Theorem D.1 this places maximum-reward weakly stable matching with two masters beyond polynomial-time approximation schemes, while existence stays polynomial.
--
--   Differences from the source:
--   - encoding: unless P = NP, no deterministic PTAS → a PTAS implies NP Sym ⊆ P Sym for every finite alphabet Sym; reason: the contrapositive; P ⊆ NP holds, so NP ⊆ P is P = NP
--   - encoding: a deterministic PTAS with unconditional existence of a weakly stable perfect matching → for each rational ε > 0 a PolyTimeComputable map that, on every domain instance with alphabet rewards that has a weakly stable perfect matching, outputs the code of one with reward ≥ (1 − ε) times every weakly stable perfect matching's reward; reason: one algorithm per fixed accuracy, required only where a stable matching exists; rational ε loses nothing since a smaller rational accuracy is stronger
--   - encoding: maximum-reward weakly stable matching → the maximum over weakly stable perfect matchings (IsSolution with every cap ⊤); reason: the domain is even and complete, and such instances have no nonperfect weakly stable matching (§C, p. 18, PDF 19)
--   - encoding: every A observer indifferent among all other agents, every B observer following one whole strict master b with all A identities first, no caps → an Instance ℤ n with every cap ⊤, the master a constant on all identities (own entries included), and b injective with b(x) < b(y) for x ∈ A, y ∈ B; reason: an observer's own entry is never compared (Blocks requires u ≠ v and a perfect matching has no fixed point), and integer ranks represent every flat or strict order on a finite set
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), p. 27 (PDF p. 28), Theorem D.6 (= Theorem 1.3, p. 2, PDF p. 3)

import Mathlib
import Definitions.Def_TwoMasterRoommates_Capped_Supplement_Hardness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped.Supplement

/-- Theorem D.6 (= Theorem 1.3), Bin Yu, STOC 2027 submission #225, p. 27 (PDF 28): a
deterministic PTAS for maximum-reward weakly stable matching in the flat/strict domain, on
instances with rewards in `{0, 21, 22, 23, 31}` that admit a weakly stable perfect matching,
implies P = NP. -/
theorem theorem_D_6 (h : HasPTAS) :
    ∀ (Sym : Type) [Fintype Sym], CookPvsNP.NP Sym ⊆ CookPvsNP.P Sym := by sorry

end TwoMasterRoommates.Capped.Supplement
