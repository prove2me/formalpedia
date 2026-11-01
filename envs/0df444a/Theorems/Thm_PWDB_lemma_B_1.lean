-- Prove2me | Theorems.Thm_PWDB_lemma_B_1
-- name    : PWDB.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:38:48.249159+00:00
-- url     : https://prove2.me/theorems/343f81fa-5092-4bfe-92e7-9c5ea55458eb
-- title:
--   Lemma B.1 — the Lagrangian dual of (D) is (P)
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, $I$ a finite index set, and $f_0, f_i : E \to \overline{\mathbb R}$ ($i \in I$) satisfy assumption (F): each $f_i$, $i \in I_0 = \{0\} \cup I$, is proper, closed and convex.
--
--   Let $f(x) = f_0(x)$ if $f_i(x) \le 0$ for all $i \in I$ and $f(x) = +\infty$ otherwise (eq. (9)). Then for every $x \in E$
--   $$
--   \sup_{\lambda \ge 0}\ \sup_{w_0, \{w_i\}}\ \Big\{ -f_0^*(w_0) - \sum_{i\in I} \lambda_i f_i^*(w_i/\lambda_i) + w_0^\top x + \sum_{i\in I} w_i^\top x \Big\} = f(x).
--   $$
--
--   So the Lagrangian dual $\inf_x \sup_{\lambda\ge0}\sup_{w}\{\dots\}$ of (D), obtained by dualizing the constraint $\sum_{i\in I_0} w_i = 0$ with multiplier $x$, is $\inf_x f(x)$, i.e. problem (P).
--
--   Differences from the source:
--   - generalization: ℝ^{dx}, ℝ^{dz} → finite-dimensional real inner product spaces E, F; reason: every ℝ^d with the dot product is such a space, so the Lean statement specializes to the printed one
--   - encoding: (F): fi proper, closed and convex, values in R̄ → TensorAHPE.IsProperClosedConvex (never −∞, somewhere finite, lower semicontinuous, convex epigraph), values in EReal; reason: for a proper function the paper's 'closed' (p.39) is lower semicontinuity; same instances
--   - reading: 'The Lagrangian dual of problem (D) is equivalent to problem (P)' → for every x, the inner suprema of the Lagrangian dual (14) equal f(x) of (9); reason: this identity is what the proof establishes (p.44) and it makes (14) literally inf_x f(x) = (P)
--   - encoding: index sets I, I0 = {0} ∪ I → Fintype ι (possibly empty), with the index 0 carried separately as f₀, w₀; reason: Lean convention; same instances
--   - encoding: convex perspective on ℝ^{dx} × ℝ₊ (Definitions A.2, A.4) → persp/pPersp with value +∞ for t < 0; reason: every multiplier in the paper is ≥ 0; no value at t ≥ 0 changes
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), Lemma B.1, p.43; displays (9), p.42, and (14) with the identity following it, p.44

import Mathlib
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_PWDB_ConvexProgram

open scoped InnerProductSpace

namespace PWDB

open Classical in
/-- **Lemma B.1** (Zhen, Kuhn & Wiesemann, arXiv:2105.00760v2, Lemma B.1, p.43, with the display in
its proof, p.44): "The Lagrangian dual of problem (D) is equivalent to problem (P)." The proof
writes the Lagrangian dual of (D) as (14), `inf_x sup_{λ≥0} sup_{{wi}} {−f0∗(w0) −
Σ_{i∈I} λi fi∗(wi/λi) + Σ_{i∈I0} wi⊤x}`, and shows: "For any fixed `x`, the embedded maximization
problems in (14) evaluate to `f(x)` as defined in (9)", where (9), p.42, is
`f(x) = f0(x)` if `fi(x) ≤ 0 ∀i ∈ I`, and `+∞` otherwise.

Under (F), for every `x`,
`sup_{λ≥0} sup_{w0, {wi}} {−f0∗(w0) − Σ_i λi fi∗(wi/λi) + w0⊤x + Σ_i wi⊤x} = f(x)`.

**Formalization Note** "Equivalent" is read as this identity of the inner suprema, the content of
the paper's proof; then (14) is `inf_x f(x)`, i.e. problem (P). `λi fi∗(wi/λi)` is the convex
perspective (Definition A.2). Values in `EReal`. (F) is `TensorAHPE.IsProperClosedConvex`. -/
theorem lemma_B_1 {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype ι]
    (f₀ : E → EReal) (f : ι → E → EReal)
    (hf₀ : TensorAHPE.IsProperClosedConvex f₀) (hf : ∀ i, TensorAHPE.IsProperClosedConvex (f i))
    (x : E) :
    (⨆ (lam : ι → ℝ) (_ : 0 ≤ lam) (w₀ : E) (w : ι → E),
        dObj f₀ f (w₀, w, lam) + ((⟪w₀, x⟫_ℝ + ∑ i, ⟪w i, x⟫_ℝ : ℝ) : EReal)) =
      if ∀ i, f i x ≤ 0 then f₀ x else ⊤ := by sorry

end PWDB
