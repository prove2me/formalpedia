-- Prove2me | Theorems.Thm_ProphetMatchingEFGT_lemma_5_6
-- name    : ProphetMatchingEFGT.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:50:03.343002+00:00
-- url     : https://prove2.me/theorems/801fa978-06ed-4b77-a0c9-53a888d173bd
-- title:
--   Lemma 5.6 — $f(x)\ge1-2c+\frac{c^2}{2}\left(\frac{1-2c}{1-c}\right)^2$
-- statement:
--   Let $0<c<\tfrac12$ and let $(a_s)_{s\in S}$, $(b_s)_{s\in S}$ be reals indexed by a finite set $S$ with
--   $$a_s,b_s\ge0,\qquad a_s+b_s\le1\ \ (s\in S),\qquad\sum_sa_s\le1,\qquad\sum_sb_s\le1.$$
--   Then
--   $$f=1-c\Big(\sum_sa_s+\sum_sb_s\Big)+c^2\Big(\frac{1-2c}{1-c}\Big)^2\Big(\sum_sa_s\cdot\sum_sb_s-\sum_sa_sb_s\Big)\ \ge\ 1-2c+\frac{c^2}{2}\Big(\frac{1-2c}{1-c}\Big)^2.$$
--
--   With $a_s=x_{us}$, $b_s=x_{vs}$ and $S=V\setminus\{u,v\}$, this is the minimization of the right side of eq. (15) over $x\in\mathcal F_M$, and it completes the proof of Lemma 5.2.
--
--   Differences from the source:
--   - generalization: f(x) for x ∈ FM, with sums over s ∈ V ∖ {u, v} → reals a, b indexed by any finite set with a_s, b_s ≥ 0, a_s + b_s ≤ 1, Σ a ≤ 1, Σ b ≤ 1; reason: these are exactly the properties the page derives from x ∈ FM (p.16); a_s = x_us, b_s = x_vs specializes it to the source
--   - reading: c is Algorithm 3's constant (1/3 or 0.337 in §5) → 0 < c < 1/2; reason: the denominators 1 − c − cΣ ≥ 1 − 2c and (1 − 2c)/(1 − c) of §5.3 presuppose c < 1/2
-- source:
--   Ezra–Feldman–Gravin–Tang, Online Stochastic Max-Weight Matching: prophet inequality for vertex and edge arrival models, arXiv:2002.09807v2, §5.3, Lemma 5.6, p. 17 (f defined as the RHS of eq. (15), p. 16)

import Mathlib

namespace ProphetMatchingEFGT

/-- **Lemma 5.6, p. 17: the minimum of `f`.**
Ezra–Feldman–Gravin–Tang, arXiv:2002.09807v2, Lemma 5.6, p. 17:
`f(x) ≥ 1 − 2c + (c²/2) · ((1 − 2c)/(1 − c))²`, where `f(x)` is the right side of eq. (15), p. 16,
`f(x) = 1 − c (Σ_s x_us + Σ_s x_vs) + c² ((1 − 2c)/(1 − c))² (Σ_s x_us · Σ_s x_vs − Σ_s x_us x_vs)`.

**Formalization Note.** Stated for reals `a_s = x_us`, `b_s = x_vs` indexed by any finite set (the
paper's `V ∖ {u, v}`) satisfying exactly the properties the page derives from `x ∈ FM` (p. 16):
`a_s, b_s ≥ 0`, `a_s + b_s ≤ 1`, `Σ_s a_s ≤ 1`, `Σ_s b_s ≤ 1`; and `c ∈ (0, 1/2)`. -/
theorem lemma_5_6 {ι : Type*} [Fintype ι] (c : ℝ) (hc0 : 0 < c) (hc : c < 1 / 2) (a b : ι → ℝ)
    (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s) (hab : ∀ s, a s + b s ≤ 1) (hsa : ∑ s, a s ≤ 1)
    (hsb : ∑ s, b s ≤ 1) :
    1 - 2 * c + c ^ 2 / 2 * ((1 - 2 * c) / (1 - c)) ^ 2 ≤
      1 - c * (∑ s, a s + ∑ s, b s) +
        c ^ 2 * ((1 - 2 * c) / (1 - c)) ^ 2 * ((∑ s, a s) * (∑ s, b s) - ∑ s, a s * b s) := by sorry

end ProphetMatchingEFGT
