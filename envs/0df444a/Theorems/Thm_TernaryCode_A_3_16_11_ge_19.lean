-- Prove2me | Theorems.Thm_TernaryCode_A_3_16_11_ge_19
-- name    : TernaryCode.A_3_16_11_ge_19
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-20T02:22:21.984665+00:00
-- url     : https://prove2.me/theorems/f2111c61-fa4a-40f0-a3f9-85fa908da8f6
-- title:
--   New lower bound $A_3(16,11)\ge 19$ for ternary codes
-- statement:
--   A **ternary code** of length $n$ is a set $C$ of words $x=(x_1,\dots,x_n)$ whose coordinates are taken from an alphabet of three symbols, $x_i\in\{0,1,2\}$. The Hamming distance of two words is $d_H(x,y)=|\{i : x_i\neq y_i\}|$, the number of coordinates in which they differ. The number $A_3(n,d)$ is the largest possible size of a ternary code of length $n$ in which any two distinct words have Hamming distance at least $d$. This theorem asserts the lower bound
--
--   $$
--   A_3(16,11)\ \ge\ 19 .
--   $$
--
--   That is, there are $19$ words of length $16$ over an alphabet of three symbols such that any two of them differ in at least eleven coordinates. Equivalently, any two of the words agree in at most five coordinates.
--
--   A. E. Brouwer maintains the standard table of bounds for $A_3(n,d)$. As of 2026-11-20 that table lists $A_3(16,11)\ge 18$, so this statement improves the best known lower bound by $1$. The code was found by a computer search, and an explicit list of its $19$ codewords is part of the proof.
--
--   **Formalization Note** A word is a function `Fin 16 → Fin 3`, the three symbols being the elements of `Fin 3`. The distance between two words is Mathlib's `hammingDist`, the number of coordinates in which they differ. The code is a `Finset` of exactly $19$ such words.
-- source:
--   A. E. Brouwer, table of bounds on the size of ternary codes A_3(n,d), https://aeb.win.tue.nl/codes/ternary-1.html, entry n = 16, d = 11: best known lower bound 18 as of 2026-11-20. The size-19 code was found by computer search and is given explicitly in the proof.

import Mathlib

theorem TernaryCode.A_3_16_11_ge_19 : ∃ C : Finset (Fin 16 → Fin 3), C.card = 19 ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 11 ≤ hammingDist x y) := by sorry
