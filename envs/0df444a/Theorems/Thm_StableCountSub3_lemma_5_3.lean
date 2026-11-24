-- Prove2me | Theorems.Thm_StableCountSub3_lemma_5_3
-- name    : StableCountSub3.lemma_5_3
-- status  : Open
-- author  : @CGTMoyano
-- created : 2026-11-24T17:53:04.08408+00:00
-- url     : https://prove2.me/theorems/6383cde1-5df7-4edd-93c5-2365b3a6600c
-- title:
--   Lemma 5.3 — the first principal cone of a simple man and the second cone of a man in $C$
-- statement:
--   Fix an instance $I$ of the stable marriage problem with $n$ men and $n$ women, a downset $D$ of the rotation poset $(\mathcal R,\preceq)$ (the reference stable matching $\mu_D$), and an outward direction $\pm$ (forward: the order $P^+(D)$ on $\mathcal R\setminus D$; backward: the reverse order $P^-(D)$ on $D$). For a man $m$ write $K_m(k)$, $S_m(k)$ and $s_m(k)$ for his $k$-th principal cone, its support (the set of men participating in its rotations) and the support size ($\infty$ when the $k$-th rotation of $m$ in the outward order does not exist). A man is *simple* if $s_m(1)=2$; $C=\{m : s_m(1)=2,\ s_m(2)=3\}$ and $B=\{m : s_m(1)=2,\ s_m(2)\ge 4\}$ (Definition 5.2). Executing a rotation means eliminating it (forward) or undoing its elimination (backward); a *swap* $(a,b)$ is a rotation whose execution exchanges the partners of the two men $a\ne b$.
--
--   **Lemma 5.3.** Let $m$ be a man.
--
--   1. If $m$ is simple, then his first principal cone consists of a single rotation $\tau$, which is his first rotation in the outward order, is a swap $(m,b)$ with some man $b\ne m$, and is a minimal element of the outward order, i.e. it can be executed immediately from $\mu_D$ in the chosen direction:
--   $$K_m(1)=\{\tau\},\qquad \tau=(m,b).$$
--   2. If $m\in C$, then there are men $a,b$ such that $m,a,b$ are distinct and
--   $$K_m(2)=\{\tau,\sigma\},\qquad \tau=(m,b),\quad \sigma=(m,a),$$
--   where $\tau$ and $\sigma$ are the first and second rotations of $m$ in the outward order; in particular $\tau$ strictly precedes $\sigma$ there, so the execution order is necessarily $\tau$ followed by $\sigma$.
--
--   The lemma identifies the first two rotations of the men with the smallest possible supports at depths one and two; it is the basis for the definition of the image $\phi(m)$ of a man $m\in C$ (Definition 5.4) and for Lemma 5.5.
--
--   **Formalization Note** Directions are `Dir.fwd` / `Dir.bwd`; $K_m(k)$ is `principalCone I D m dir k` (an `Option`, `none` when the $k$-th rotation does not exist), the $k$-th rotation is `kth I D m dir k`, the swap $(m,b)$ executed in direction `dir` is `IsSwapOn dir τ m b`, "executable immediately" is `IsMinOut I D dir τ`, and "$\tau$ before $\sigma$" is `outLT I dir τ σ`. Distinctness of $m$ from $a$ and $b$ is part of `IsSwapOn`.
-- source:
--   Kawarabayashi, Wada, Yoneda 2026, A Sub-3^n Upper Bound on the Number of Stable Matchings, arXiv:2611.06604v1, Lemma 5.3, p. 27 (Section 5.2), with Definition 5.2

import Mathlib
import Definitions.Def_StableCountSub3_Credits

open StableMatching

namespace StableCountSub3

/-- Lemma 5.3: the first principal cone of a simple man is a single swap that can be executed
immediately from `μ_D` in the chosen direction; if `m ∈ C`, then `K_m(2) = {τ, σ}` with
`τ = (m, b)`, `σ = (m, a)` swaps, `m, a, b` distinct, and `τ` executed before `σ`. -/
theorem lemma_5_3 {n : ℕ} (I : Instance n) (D : Finset (Rot n)) (hD : IsDownset I D)
    (m : Fin n) (dir : Dir) :
    (IsSimple I D m dir →
      ∃ (b : Fin n) (τ : Rot n), kth I D m dir 1 = some τ ∧
        principalCone I D m dir 1 = some {τ} ∧ IsSwapOn dir τ m b ∧ IsMinOut I D dir τ) ∧
    (InC I D m dir →
      ∃ (a b : Fin n) (τ σ : Rot n), a ≠ b ∧
        kth I D m dir 1 = some τ ∧ kth I D m dir 2 = some σ ∧
        principalCone I D m dir 2 = some {τ, σ} ∧
        IsSwapOn dir τ m b ∧ IsSwapOn dir σ m a ∧ outLT I dir τ σ) := by sorry

end StableCountSub3
