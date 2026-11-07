-- Prove2me | Theorems.Thm_RevisitXor_eq_2
-- name    : RevisitXor.eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:05:56.656103+00:00
-- url     : https://prove2.me/theorems/b0d7e632-5c0a-4276-9dd0-3f87f27ae00d
-- title:
--   Identity (2): $M\cdot C_\Pi(h)=w(X_1,\dots,X_{M/2})=W$
-- statement:
--   Let $M=2^m$, $h:[2]^{2m}\to[2]$, and let $\pi$ be a fixed-point-free involution of $[2]^m$ with edges $X_1,\dots,X_{M/2}$ listed in any order. Then the correlation between $h$ and $f_\pi$ is the weight of the matching, up to scaling:
--
--   $$M\cdot\operatorname{corr}(h,f_\pi)=w(X_1,X_2,\dots,X_{M/2})=W. \tag{2}$$
--
--   It turns the tail bound (1) into a concentration bound for the weight of a uniformly random perfect matching.
--
--   **Formalization Note** The edges of $\pi$ are a valid edge sequence `xs` in which every edge $\{y,\pi y\}$ occurs.
--
--   Differences from the source:
--   - encoding: X₁, …, X_{M/2}, the edges of π → a valid edge sequence xs with xs j = {y, π y} for some j, for every y; reason: a valid sequence of M/2 disjoint edges containing every edge of π lists exactly the edges of π
-- source:
--   Viola, Revisiting the XOR lemma, STOC 2027 submission (manuscript of August 25, 2026, sha256 3b49e10d…716), §1, (2), p.6

import Mathlib
import Definitions.Def_RevisitXor_corr
import Definitions.Def_RevisitXor_mm
import Definitions.Def_RevisitXor_validSeqs

namespace RevisitXor

open OAI.MatchingSmoothing

/-- **Identity (2): the correlation is the weight of the matching.** Viola, *Revisiting the XOR lemma*, STOC 2027 submission (manuscript of August 25, 2026, sha256
3b49e10d…716), §1, (2), p.6: "The correlation between h and the function f corresponding to π is just the
sum of the weights, up to scaling: M · C_Π(h) = w(X1, X2, . . . , XM/2) =: W (2) where the sum is
over all edges in (the graph corresponding to) π."

**Formalization Note.** `M = 2^m`, `h` is read on `[2]^m × [2]^m`, and the correlation is the
signed one. The edges `X₁, …, X_{M/2}` of `π` are a valid edge sequence `xs` in which every edge
`{y, π y}` of `π` occurs. -/
theorem eq_2 {m : ℕ} (h : Cube m × Cube m → ZMod 2) (π : Pairing (Cube m))
    (xs : Fin (2 ^ m / 2) → Sym2 (Cube m)) (hxs : xs ∈ validSeqs m)
    (hπ : ∀ y : Cube m, ∃ j, xs j = s(y, π.1 y)) :
    (2 : ℝ) ^ m * corr h (mm π) = W h xs := by sorry

end RevisitXor
