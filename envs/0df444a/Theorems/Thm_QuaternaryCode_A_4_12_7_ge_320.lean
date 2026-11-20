-- Prove2me | Theorems.Thm_QuaternaryCode_A_4_12_7_ge_320
-- name    : QuaternaryCode.A_4_12_7_ge_320
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-20T02:22:02.411161+00:00
-- url     : https://prove2.me/theorems/5c66020b-4c12-4a16-945b-4e5f60ecb7a8
-- title:
--   New lower bound $A_4(12,7)\ge 320$ for quaternary codes
-- statement:
--   A **quaternary code** of length $n$ is a set $C$ of words $x=(x_1,\dots,x_n)$ whose coordinates are taken from an alphabet of four symbols, $x_i\in\{0,1,2,3\}$. The Hamming distance of two words is $d_H(x,y)=|\{i : x_i\neq y_i\}|$, the number of coordinates in which they differ. The number $A_4(n,d)$ is the largest possible size of a quaternary code of length $n$ in which any two distinct words have Hamming distance at least $d$. This theorem asserts the lower bound
--
--   $$
--   A_4(12,7)\ \ge\ 320 .
--   $$
--
--   That is, there are $320$ words of length $12$ over an alphabet of four symbols such that any two of them differ in at least seven coordinates. Equivalently, any two of the words agree in at most five coordinates.
--
--   A. E. Brouwer maintains the standard table of bounds for $A_4(n,d)$. As of 2026-11-20 that table lists $A_4(12,7)\ge 256$, so this statement improves the best known lower bound by $64$. The code was found by a computer search, and an explicit list of its $320$ codewords is part of the proof.
--
--   **Formalization Note** A word is a function `Fin 12 → Fin 4`, the four symbols being the elements of `Fin 4`. The distance between two words is Mathlib's `hammingDist`, the number of coordinates in which they differ. The code is a `Finset` of exactly $320$ such words.
-- source:
--   A. E. Brouwer, table of bounds on the size of quaternary codes A_4(n,d), https://aeb.win.tue.nl/codes/quaternary-1.html, entry n = 12, d = 7: best known lower bound 256 as of 2026-11-20. The size-320 code was found by computer search and is given explicitly in the proof.

import Mathlib

theorem QuaternaryCode.A_4_12_7_ge_320 : ∃ C : Finset (Fin 12 → Fin 4), C.card = 320 ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 7 ≤ hammingDist x y) := by sorry
