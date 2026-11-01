-- Prove2me | Theorems.Thm_TimeVaryingGames_lemma_A_4
-- name    : TimeVaryingGames.lemma_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:30:30.878186+00:00
-- url     : https://prove2.me/theorems/0e32a638-5aa5-4e68-97cc-4ef40f03f0d4
-- title:
--   Lemma A.4, p.31: the template inequality (A.12) for prox sequences
-- statement:
--   Let $h$ be a distance-generating function with modulus $K$ on a compact convex set $\mathcal C$, with Bregman divergence $D$ and prox-mapping $\mathcal P$. Let $Y_t$ be dual vectors and $X_{t+1}=\mathcal P(X_t;Y_t)$ with $X_1\in\mathcal C_h$. Then for all $x\in\mathcal C$, every window $\mathcal T=[\tau_{\rm start}\,..\,\tau_{\rm end}]$ and every sequence $\alpha_t\ge0$ on $\mathcal T$,
--   $$\sum_{t\in\mathcal T}\alpha_t\langle Y_t,x-X_t\rangle\le\sum_{t\in\mathcal T}(\alpha_t-\alpha_{t-1})D(x,X_t)+\frac1{2K}\sum_{t\in\mathcal T}\alpha_t\|Y_t\|_*^2,$$
--   with the convention $\alpha_{\tau_{\rm start}-1}=0$.
--
--   This weighted regret-type bound for prox sequences is the template from which energy and regret inequalities for mirror descent are derived.
--
--   **Formalization Note** Indices start at $0$ in Lean; the convention $\alpha_{\tau_{\rm start}-1}=0$ is an explicit case split.
--
--   Differences from the source:
--   - encoding: stages t = 1, 2, … → t : ℕ starting at 0 (Lean's t is stage t + 1); reason: index shift; same sequences
--   - encoding: h : X → ℝ ∪ {∞} with dom h = C; ∂h(x) tested against all x′ ∈ X → h : E → ℝ with only its values on C used; the subgradient inequality tested for x′ ∈ C; reason: h = +∞ off C, so the inequality is automatic off C: the same subdifferential and prox-domain
--   - encoding: there exists a continuous selection ∇h of ∂h on dom ∂h → the selection is a parameter gradh with ContinuousOn and gradh x ∈ ∂h(x) on the prox-domain; reason: D and P are defined through the selection, so it must be fixed data
--   - encoding: the prox-mapping P(x; y) = argmin (13) as a function → the relation IsProxPoint (xp ∈ C minimizes (13)); reason: the minimizer exists and is unique for a DGF, so the relation is the graph of P
--   - encoding: K-strongly convex with modulus K (divided by in (A.5b), (40)) → 0 < Kc is part of IsDGF; reason: a strong-convexity modulus is positive; the paper divides by it
--   - encoding: the convention α_{τ_start−1} = 0 → the coefficient (α t − if t = τs then 0 else α (t − 1)) on Finset.Icc τs τe; reason: the same coefficients; for t > τs the subtraction t − 1 is exact, and an empty window gives 0 ≤ 0
-- source:
--   Duvocelle, Mertikopoulos, Staudigl, Vermeulen, Multi-Agent Online Learning in Time-Varying Games, arXiv:1809.03066v3, Appendix A, Lemma A.4, p.31, eqs. (A.11)–(A.12)

import Mathlib
import Definitions.Def_TimeVaryingGames_DGF

namespace TimeVaryingGames

/-- **Lemma A.4 (template inequality).**
arXiv:1809.03066v3, Appendix A, p.31: "Lemma A.4. Consider a sequence of dual vectors Y_t ∈ Y,
t = 1, 2, . . . , and let X_{t+1} = P(X_t; Y_t) (A.11) with X_1 ∈ C_h initialized arbitrarily.
Then, for all x ∈ C and every nonnegative sequence α_t ≥ 0 defined over the window
T = [τ_start . . τ_end], we have
Σ_{t∈T} α_t⟨Y_t, x − X_t⟩ ≤ Σ_{t∈T} (α_t − α_{t−1})D(x, X_t) + (1/2K) Σ_{t∈T} α_t‖Y_t‖²_*, (A.12)
with the convention that α_{τ_start−1} = 0 in the above sum."

**Formalization Note.** Lean's index `t : ℕ` starts at `0` (`X 0` is the paper's `X_1`). The
window is `Finset.Icc τs τe`; the convention `α_{τs−1} = 0` is written as the
`if t = τs then 0 else α (t - 1)` term (for `t > τs` the subtraction `t - 1` is exact). The values
of `α` outside the window are irrelevant. -/
theorem lemma_A_4 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {C : Set E} {Kc : ℝ} {h : E → ℝ} {gradh : E → E →L[ℝ] ℝ} (hdgf : IsDGF C Kc h gradh)
    (Y : ℕ → E →L[ℝ] ℝ) (X : ℕ → E) (hX0 : X 0 ∈ proxDomain C h)
    (hX : ∀ t, IsProxPoint C h gradh (X t) (Y t) (X (t + 1)))
    {x : E} (hx : x ∈ C) (τs τe : ℕ) (α : ℕ → ℝ)
    (hα : ∀ t ∈ Finset.Icc τs τe, 0 ≤ α t) :
    ∑ t ∈ Finset.Icc τs τe, α t * Y t (x - X t) ≤
      ∑ t ∈ Finset.Icc τs τe,
          (α t - (if t = τs then 0 else α (t - 1))) * bregman h gradh x (X t) +
        1 / (2 * Kc) * ∑ t ∈ Finset.Icc τs τe, α t * ‖Y t‖ ^ 2 := by sorry

end TimeVaryingGames
