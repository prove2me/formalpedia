-- Prove2me | Theorems.Thm_PConeEB_lemma_4_1
-- name    : PConeEB.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:32:36.50648+00:00
-- url     : https://prove2.me/theorems/c83ba385-e95a-4b44-8e2a-70a4925880bd
-- title:
--   Lemma 4.1 — the bound (4.2) and the Hölder equality case
-- statement:
--   Let $p,q\in(1,\infty)$ with $\frac1p+\frac1q=1$, and let $\zeta\in\mathbb R^n$ ($n\ge1$) satisfy $\|\zeta\|_q=1$. Define $\bar\zeta:=-\operatorname{sgn}(\zeta)\circ|\zeta|^{q-1}$. Then:
--
--   1. $\|\bar\zeta\|_p=1$;
--   2. there exist $C>0$ and $\epsilon>0$ such that, with $I=\{i:\bar\zeta_i\ne0\}$,
--   $$
--   1+\langle\zeta,\omega\rangle\ge C\sum_{i\in I}|\omega_i-\bar\zeta_i|^2+\frac1p\sum_{i\notin I}|\omega_i|^p\qquad\text{whenever }\|\omega-\bar\zeta\|\le\epsilon\text{ and }\|\omega\|_p=1;
--   $$
--   3. for any $\omega$ with $\|\omega\|_p\le1$, one has $\langle\zeta,\omega\rangle\ge-1$, with equality if and only if $\omega=\bar\zeta$.
--
--   The inequality (4.2) quantifies the equality case of Hölder's inequality; its two sums, of order two on $I$ and of order $p$ off $I$, are the source of the two exponents $\frac12$ and $\frac1p$.
--
--   Differences from the source:
--   - encoding: ζ, ω ∈ ℝⁿ, i ∉ I → EuclideanSpace ℝ (Fin n), the filter by ¬ (zetaBar q ζ i ≠ 0); reason: Lean conventions; ‖ω − ζ̄‖ is the Euclidean norm, as on the page
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, Lemma 4.1, (4.2), p.17

import Mathlib
import Definitions.Def_PConeEB_pNorm
import Definitions.Def_PConeEB_zetaBar

namespace PConeEB

/-- Lemma 4.1. For `1/p + 1/q = 1`, `n ≥ 1`, `ζ ∈ ℝⁿ` with `‖ζ‖_q = 1` and
`ζ̄ := -sgn(ζ) ∘ |ζ|^{q-1}`: `‖ζ̄‖_p = 1`; there are `C, ε > 0` with
`1 + ⟨ζ, ω⟩ ≥ C ∑_{i∈I} |ωᵢ - ζ̄ᵢ|² + (1/p) ∑_{i∉I} |ωᵢ|^p` whenever `‖ω - ζ̄‖ ≤ ε` and `‖ω‖_p = 1`,
where `I = {i : ζ̄ᵢ ≠ 0}`; and `⟨ζ, ω⟩ ≥ -1` whenever `‖ω‖_p ≤ 1`, with equality iff `ω = ζ̄`.
Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, Lemma 4.1, (4.2), p.17.

**Formalization Note.** `‖ω - ζ̄‖` is the Euclidean norm. `C, ε` may depend on all the data, in
particular on `ζ`, as on the page. -/
theorem lemma_4_1 {n : ℕ} (hn : 1 ≤ n) {p q : ℝ} (hp : 1 < p) (hpq : 1 / p + 1 / q = 1)
    (ζ : EuclideanSpace ℝ (Fin n)) (hζ : pNorm q ζ.ofLp = 1) :
    pNorm p (zetaBar q ζ).ofLp = 1 ∧
      (∃ C : ℝ, 0 < C ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ ω : EuclideanSpace ℝ (Fin n),
        ‖ω - zetaBar q ζ‖ ≤ ε → pNorm p ω.ofLp = 1 →
          C * ∑ i ∈ Finset.univ.filter (fun i => zetaBar q ζ i ≠ 0),
                |ω i - zetaBar q ζ i| ^ 2 +
              1 / p * ∑ i ∈ Finset.univ.filter (fun i => ¬ zetaBar q ζ i ≠ 0), |ω i| ^ p ≤
            1 + inner ℝ ζ ω) ∧
      ∀ ω : EuclideanSpace ℝ (Fin n), pNorm p ω.ofLp ≤ 1 →
        -1 ≤ inner ℝ ζ ω ∧ (inner ℝ ζ ω = -1 ↔ ω = zetaBar q ζ) := by sorry

end PConeEB
