-- Prove2me | Theorems.Thm_ReadTwiceCount_lemma_6_1
-- name    : ReadTwiceCount.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:43:06.65682+00:00
-- url     : https://prove2.me/theorems/1113b2bd-8497-45c5-a125-68a012f2cd08
-- title:
--   Lemma 6.1 — the block error certificate $0\le U-y(H,h)\le a/2+\sum_{i\in E}D_i\eta_i$
-- statement:
--   **Lemma 6.1.** Fix a global clause bound $n\ge1$, $B=n+1$, a read-twice normalized state $H$ with $s\le n$ clauses, a positive dangling query $h$, a density $0<a<1$, and a positive block of $(H,h)$ meeting the stopping rule with $\delta=a/B^3$. Write $E$ for its EQ boundary inputs, $y_i$ for their true coordinates and $D_i$ for their frozen weights. Suppose each EQ boundary is given a lower value satisfying
--   $$1\le\ell_i\le y_i,\qquad y_i-\ell_i\le\eta_i .$$
--   Let $U$ be the block value with these lower boundary values and the retained upper cuts. Then
--   $$0\le U-y(H,h)\le\frac a2+\sum_{i\in E}D_i\eta_i .$$
--
--   The weights are frozen before the boundary values are known; the lemma makes them valid for the combined error of all boundary approximations.
--
--   Differences from the source:
--   - reading: the lemma's context: a positive dangling state, global $n\ge1$ bounding its clause count, an active density, the block built with threshold (12) → hypotheses $n\ge1$, $s\le n$, $0<a<1$, read-twice normalized positive dangling $(H,h)$, and the stopping rule $D_u\le(a/(n+1)^3)^2$ for every cut; reason: the paper states these once (§3, p.4; §5, p.6: only calls with $0<a<1$ require approximation; §5.1, (12)); they are the setting of §6
--   - generalization: the block produced by the procedure's fixed deterministic expansion order → any positive block of $(H,h)$ meeting the stopping rule; reason: the paper's block is one of these, and the proof uses only that the block is positive and meets the stopping rule
-- source:
--   He, A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments, STOC 2027 submission (manuscript sha256 7a2a9dcd…), Lemma 6.1, displays (22)–(23), p.9; context §3, p.4 and §5.1, display (12), p.7

import Mathlib
import Definitions.Def_ReadTwiceCount_IsPositiveBlock

namespace ReadTwiceCount

/-- **Lemma 6.1** (He, *A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments*, STOC 2027
submission (manuscript sha256 7a2a9dcd…), Lemma 6.1, p.9): "Suppose each EQ boundary
is given a lower value satisfying 1 ≤ ℓᵢ ≤ yᵢ, yᵢ − ℓᵢ ≤ ηᵢ. (22) Let U be the block value with these
lower boundary values and the retained upper cuts. Then 0 ≤ U − y(H, h) ≤ a/2 + Σ_{i∈E} Dᵢηᵢ." (23)

The context of §§3–6: a global clause bound `n ≥ 1` (B = n + 1), a positive dangling query `(H, h)`
of a read-twice normalized state with `s ≤ n` clauses, an active density `0 < a < 1`, and a positive
block of `(H, h)` meeting the stopping rule with `δ = a/B³` (12). `yᵢ` is the true coordinate of the
boundary's state, and `Dᵢ` its frozen path derivative.

**Formalization Note** `ηᵢ` is any real; (22) forces `ηᵢ ≥ 0`. -/
theorem lemma_6_1 {M : ℕ} (n : ℕ) (hn : 1 ≤ n) (H : Formula M) (h : Lit M) (hRT : ReadTwice H)
    (hN : Normalized H) (hD : IsDangling H h) (hP : IsPositive H h) (hs : H.clauses.length ≤ n)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (T : DTree) (hT : IsPositiveBlock H h T)
    (hstop : StoppingRule n a H h T) (ℓ η : List ℕ → ℝ)
    (hℓ : ∀ i ∈ T.boundaries,
      1 ≤ ℓ i ∧ ℓ i ≤ trueInput H h i ∧ trueInput H h i - ℓ i ≤ η i) :
    0 ≤ blockValue H h T ℓ - (yCoord H h : ℝ) ∧
      blockValue H h T ℓ - (yCoord H h : ℝ) ≤ a / 2 + ∑ i ∈ T.boundaries, frozenD H h T i * η i := by sorry

end ReadTwiceCount
