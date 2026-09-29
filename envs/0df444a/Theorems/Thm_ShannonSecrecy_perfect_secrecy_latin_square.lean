-- Prove2me | Theorems.Thm_ShannonSecrecy_perfect_secrecy_latin_square
-- name    : ShannonSecrecy.perfect_secrecy_latin_square
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T18:43:02.854286+00:00
-- url     : https://prove2.me/theorems/149e9c95-8f37-41c8-81fc-83006b9740d3
-- title:
--   Minimal perfect systems are Latin squares with equiprobable keys
-- statement:
--   **Shannon 1949, §10, p. 681.** *Perfect systems in which the number of cryptograms, the number of messages, and the number of keys are all equal are characterized by the properties that (1) each message is connected to each cryptogram by exactly one line, and (2) all keys are equally likely; thus the matrix representation of the system is a "Latin square".*
--
--   Concretely: let a finite secrecy system have perfect secrecy and satisfy $|M| = |K| = |E|$. Then
--
--   1. for every message $M$ and every cryptogram $E$ there is exactly one key $k$ with $T_k M = E$, and
--   2. all keys have the same a priori probability (necessarily $1/|K|$).
--
--   Consequently the $|M| \times |E|$ table whose $(M, E)$ entry is the unique key carrying $M$ to $E$ is a Latin square: each key occurs exactly once in each row and once in each column. This identifies the minimal perfect systems — those meeting the bound "as many keys as messages" — up to relabelling.
--
--   **Formalization Note** "Exactly one line from $M$ to $E$" is the unique-existence of a key $k$ with $T_k M = E$; "all keys equally likely" is stated as the equality of the a priori probabilities of any two keys, from which the value $1/|K|$ follows by normalization. The cardinality hypotheses are exactly Shannon's "the number of cryptograms, the number of messages, and the number of keys are all equal".
-- source:
--   C. E. Shannon, "Communication Theory of Secrecy Systems", Bell System Technical Journal 28(4):656-715, 1949; https://doi.org/10.1002/j.1538-7305.1949.tb00928.x, p. 681 (Part II, §10 Perfect Secrecy, the paragraph characterizing perfect systems as Latin squares)

import Definitions.Def_shannon_secrecy_system

namespace ShannonSecrecy

theorem perfect_secrecy_latin_square
    {M K E : Type*} [Fintype M] [Fintype K] [Fintype E] [DecidableEq E]
    (C : Cipher M K E) (h : PerfectSecrecy C)
    (hMK : Fintype.card M = Fintype.card K) (hKE : Fintype.card K = Fintype.card E) :
    (∀ (m : M) (e : E), ∃! k : K, C.encipher k m = e) ∧
      ∀ k k' : K, C.keyProb k = C.keyProb k' := by sorry

end ShannonSecrecy
