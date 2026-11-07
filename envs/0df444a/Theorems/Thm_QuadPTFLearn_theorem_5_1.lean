-- Prove2me | Theorems.Thm_QuadPTFLearn_theorem_5_1
-- name    : QuadPTFLearn.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:22:54.246506+00:00
-- url     : https://prove2.me/theorems/c0aa86b6-da81-4bbf-8268-a169dba3b4a7
-- title:
--   Theorem 5.1, p.32 — a degree-$2k$ certificate $h_r(v\cdot x)p(w)$ with correlation $\Omega(\alpha^{2^{O(k)}})$ along a direction with $\mathrm{Rand}_f(v)\ge\alpha$
-- statement:
--   Let $v\in S^{d-1}$, $w=\mathrm{proj}_{v^\perp}(x)$, let $q_1,\dots,q_k$ be polynomials of degree at most two and $g:v^\perp\to\{0,1\}$, and
--   $$f(x)=g(w)\,1\{q_1(x)\ge0,\dots,q_k(x)\ge0\}.$$
--   There are universal constants $c>0$ and $C$ such that, if $\mathrm{Rand}_f(v)\ge\alpha$ for some $\alpha\in(0,1)$, then there exist $r\in\{1,\dots,2k\}$ and a polynomial $p(w)$ on $v^\perp$ with $\|p\|_2=1$ and $r+\deg p\le2k$ such that
--   $$\mathbb E_{x\sim N(0,I)}\big[f(x)\,h_r(v\cdot x)\,p(w)\big]\ \ge\ c\,\alpha^{2^{Ck}} .$$
--
--   This is the main structural result: a direction along which $f$ has non-negligible randomized error is detected by a low-degree moment of the label, which is what the spectral algorithm of Section 6 estimates.
--
--   Differences from the source:
--   - reading: Ω(α^{2^{O(k)}}) → c·α^{2^{C·k}} with universal c > 0 and C chosen before d, k, f, v, α; reason: constants depending on k or f would be a weaker reading
--   - encoding: g(w) : v⊥ → {0,1} → a measurable {0,1}-valued g on ℝᵈ evaluated at x − ⟪v,x⟫v; reason: w = proj_{v⊥}x; measurability makes the expectation and Rand_f defined
--   - encoding: p(w) : v⊥ → ℝ with ∥p∥ = 1 and deg(p) → a polynomial P on ℝᵈ with P(x) = P(x − ⟪v,x⟫v), Gaussian L² norm 1, total degree; reason: polynomials on v⊥ are exactly these, and w ∼ N(0, I_{v⊥}) is the image of N(0, I_d)
--   - encoding: q_i a degree-2 polynomial → total degree ≤ 2; reason: Definition 1.1 ("of degree at most two")
--   - encoding: i ∈ [k], k ∈ ℤ₊ → k a natural number, k = 0 not excluded; reason: at k = 0 f = g(w) does not depend on v, so Rand_f(v) = 0 < α and the statement is vacuous; no instance of the source changes
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Theorem 5.1, p.32 (PDF p.34)

import Mathlib
import Definitions.Def_QuadPTFLearn_Gaussian

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace QuadPTFLearn

/-- I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Theorem 5.1, p.32 (PDF p.34).

There are universal constants `c > 0` and `C` such that the following holds. Let
`f(x) = g(w) 1{q₁(x) ≥ 0, …, q_k(x) ≥ 0}` with `deg qᵢ ≤ 2`, `v` a unit vector,
`w = proj_{v⊥}(x)` and `g : v⊥ → {0, 1}`. If `Rand_f(v) ≥ α` for some `α ∈ (0, 1)`, then there
are `r ∈ [2k]` and a polynomial `p` on `v⊥` with `‖p‖₂ = 1`, `r + deg p ≤ 2k` and
`E_{x∼N(0,I)}[f(x) h_r(v · x) p(w)] ≥ c α^{2^{Ck}}`.

**Formalization Note.** `Ω(α^{2^{O(k)}})` is read with universal constants chosen before
`d, k, f, v, α`. `g` is a measurable `{0,1}`-valued function evaluated at `proj_{v⊥} x`. -/
theorem theorem_5_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℕ,
      ∀ (d k : ℕ) (q : Fin k → Poly d), IsQuadFamily q →
      ∀ g : Pt d → ℝ, Measurable g → IsBoolean g →
      ∀ v : Pt d, ‖v‖ = 1 → ∀ α : ℝ, 0 < α → α < 1 →
        α ≤ Rand (fun x => g (perp v x) * ptfInd q x) v →
        ∃ r : ℕ, 1 ≤ r ∧ r ≤ 2 * k ∧ ∃ p : Poly d, IsOnPerp v p ∧ l2norm (peval p) = 1 ∧
          r + p.totalDegree ≤ 2 * k ∧
          c * α ^ (2 ^ (C * k)) ≤
            ∫ x, g (perp v x) * ptfInd q x * hnorm r ⟪v, x⟫ * peval p x ∂gauss d := by sorry

end QuadPTFLearn
