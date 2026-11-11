-- Prove2me | Theorems.Thm_TernarySync_Alphabet_proposition_3_1
-- name    : TernarySync.Alphabet.proposition_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:53:37.707686+00:00
-- url     : https://prove2.me/theorems/b1907574-fb7c-4222-8223-b27be5a6ccad
-- title:
--   Proposition 3.1 — the six codewords form an 18-Brinkhuis 2-triple; $W(T,R)$ is square-free; $R \mapsto W(T,R)$ is injective
-- statement:
--   Let $B_{a,r}$ ($a \in \{0,1,2\}$, $r \in \{0,1\}$) be the six length-18 words of Equation (7) and, for an outer word $T = T_1 \cdots T_N$ over $\{0,1,2\}$ and $R \in \{0,1\}^N$, let $W(T,R) = B_{T_1,R_1} \cdots B_{T_N,R_N}$ (Equation (8)). Then:
--
--   1. the sets $C_a = \{B_{a,0}, B_{a,1}\}$ form an $18$-Brinkhuis $2$-triple (Definition 1.3);
--   2. for every ternary square-free word $T$ (of any length $N$) and every $R \in \{0,1\}^N$, the word $W(T,R)$ is square-free;
--   3. for each fixed $T$, the map $R \mapsto W(T,R)$ is injective.
--
--   $$T \text{ square-free} \implies W(T,R) \text{ square-free for all } R \in \{0,1\}^N, \qquad R \mapsto W(T,R) \text{ injective}.$$
--
--   This is the classical preservation property of the corrected Ekhad–Zeilberger construction, together with the recovery of the choices from the output: every assignment of the $N$ independent bits yields a distinct square-free ternary word.
--
--   **Formalization Note.** `ezTriple a` is $C_a$; `T : List (Fin 3)`, `R : Fin T.length → Fin 2`.
--
--   Differences from the source:
--   - encoding: R ∈ {0,1}^N, C_a ⊆ {0,1,2}^18 → R : Fin T.length → Fin 2; C_a a Finset of lists of length 18 over Fin 3; reason: Lean representation of the same sets
-- source:
--   Xu, Fu, Qiao, Tao, Synchronization Strings over a Ternary Alphabet, STOC 2027 submission (manuscript sha256 1b74ae6d…), p. 14 (PDF 15), Proposition 3.1

import Mathlib
import Definitions.Def_TernarySync_Alphabet_Brinkhuis

set_option autoImplicit false

namespace TernarySync.Alphabet

/-- Proposition 3.1 (p. 14): the six words of Equation (7) form an 18-Brinkhuis 2-triple; for
every ternary square-free word `T` and every `R ∈ {0, 1}^{|T|}` the word `W(T, R)` of
Equation (8) is square-free; and for each fixed `T` the map `R ↦ W(T, R)` is injective. -/
theorem proposition_3_1 :
    IsBrinkhuisTriple 18 2 ezTriple ∧
      (∀ T : List (Fin 3), IsSquareFree T → ∀ R : Fin T.length → Fin 2, IsSquareFree (W T R)) ∧
      (∀ T : List (Fin 3), Function.Injective (W T)) := by sorry

end TernarySync.Alphabet
