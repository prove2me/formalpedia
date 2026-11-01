-- Prove2me | Theorems.Thm_ProcessingNetworks_PathCompact_lemma_A_12
-- name    : ProcessingNetworks.PathCompact.lemma_A_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:30:05.450848+00:00
-- url     : https://prove2.me/theorems/7a8eaa5d-a1f9-4e44-9087-965be2a5daab
-- title:
--   Lemma A.12 — calculus of Dini derivatives: negation, sums and the chain rule (A.11)–(A.15)
-- statement:
--   Write $D^+f(t)=\limsup_{h\downarrow0}\frac{f(t+h)-f(t)}{h}$ and $D^-f(t)=\liminf_{h\downarrow0}\frac{f(t+h)-f(t)}{h}$, values in $[-\infty,\infty]$. For all functions $f,f_1,f_2$ on $\mathbb R_+$ and every $t\ge0$:
--
--   1. (A.11) $\;D^-(-f)(t)=-D^+f(t)$;
--   2. (A.12) $\;D^+(f_1+f_2)(t)\le D^+f_1(t)+D^+f_2(t)$, whenever the right side is defined (not $\infty+(-\infty)$);
--   3. (A.13) $\;D^-(f_1+f_2)(t)\ge D^-f_1(t)+D^-f_2(t)$.
--
--   Furthermore, if $f:\mathbb R_+\to\mathbb R$ is continuous and $g:\mathbb R\to\mathbb R$ is continuously differentiable and nondecreasing, then
--
--   4. (A.14) $\;D^+(g\circ f)(t)=g'(f(t))\,D^+f(t)$, and
--   5. (A.15) $\;D^-(g\circ f)(t)=g'(f(t))\,D^-f(t)$,
--
--   each whenever its right side is defined (not $0\cdot(\pm\infty)$).
--
--   These rules are used repeatedly in the proofs of Lemmas 10.8 and 10.13 to compute Dini derivatives of Lyapunov functions along fluid paths.
--
--   **Formalization Note** The upper derivative is the published `ProcessingNetworks.LyapunovCriteria.diniUpperRight`, the lower one `diniLowerRight`; both are `EReal`-valued and take $f:\mathbb R\to\mathbb R$.
--
--   Differences from the source:
--   - encoding: f, f₁, f₂ : ℝ₊ → ℝ, f continuous on ℝ₊ → f, f₁, f₂ : ℝ → ℝ evaluated at t ≥ 0, f continuous on [0, ∞) (ContinuousOn f (Set.Ici 0)); reason: at t ≥ 0 the Dini derivatives use only values on [t, ∞); every function on ℝ₊ extends to ℝ and every function on ℝ restricts, with the same Dini derivatives; same instances
--   - encoding: Dini derivatives with values in [−∞, ∞] → EReal; reason: Lean convention; same values
--   - encoding: (A.12) as printed → (A.12) under the hypotheses D⁺f₁(t) ≠ −∞ ∨ D⁺f₂(t) ≠ +∞ and D⁺f₁(t) ≠ +∞ ∨ D⁺f₂(t) ≠ −∞; reason: a nondegeneracy condition that only excludes the undefined right side ∞ + (−∞) (which EReal evaluates to ⊥, making the clause false, e.g. f₁ = √·, f₂ = −√· at 0); every defined case is kept (paper.md reading 3)
--   - encoding: (A.13) as printed → (A.13) with no condition; reason: in the undefined case ∞ + (−∞) the right side evaluates to ⊥ in EReal, where the inequality holds; every defined case is the book's
--   - encoding: (A.14), (A.15) as printed → (A.14), (A.15) under the hypothesis g′(f(t)) ≠ 0 or the Dini derivative of f at t is finite; reason: a nondegeneracy condition that only excludes the undefined right side 0·(±∞) (which EReal evaluates to 0, making the clause false, e.g. f = ∛·, g = (·)³ at 0); every defined case, including ±∞ when g′(f(t)) > 0, is kept (paper.md reading 3)
--   - encoding: g continuously differentiable and nondecreasing, g′ → ContDiff ℝ 1 g, Monotone g, deriv g; reason: Lean convention; same functions
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Appendix A, §A.4, Lemma A.12, eqs. (A.11)–(A.15), p.263 (PDF 279); Dini derivatives (A.9)–(A.10), p.262 (PDF 278)

import Mathlib
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_DiniDerivative
import Definitions.Def_ProcessingNetworks_PathCompact_diniLowerRight

open Filter Topology

namespace ProcessingNetworks.PathCompact

open ProcessingNetworks.LyapunovCriteria

/-- **Lemma A.12** (calculus of Dini derivatives), Dai & Harrison, *Processing Networks*
(pre-publication draft 2020-4-2, spnbook.org), Appendix A, §A.4, Lemma A.12, eqs. (A.11)–(A.15),
p.263 (PDF 279), with the Dini derivatives (A.9)–(A.10) of p.262 (PDF 278).

For any functions `f, f₁, f₂` and every `t ≥ 0`:
1. (A.11) `D₋(−f)(t) = −D⁺f(t)`;
2. (A.12) `D⁺(f₁ + f₂)(t) ≤ D⁺f₁(t) + D⁺f₂(t)`, whenever the right side is not of the form
   `∞ + (−∞)`;
3. (A.13) `D₋(f₁ + f₂)(t) ≥ D₋f₁(t) + D₋f₂(t)`;
4. (A.14) if `f` is continuous on `ℝ₊` and `g : ℝ → ℝ` is continuously differentiable and
   nondecreasing, `D⁺(g ∘ f)(t) = g′(f(t)) · D⁺f(t)`, whenever the right side is not of the form
   `0 · (±∞)`;
5. (A.15) under the same assumptions, `D₋(g ∘ f)(t) = g′(f(t)) · D₋f(t)`, whenever the right side
   is not of the form `0 · (±∞)`.

**Formalization Note.** Dini derivatives are `EReal`-valued (`diniUpperRight`, published, and
`diniLowerRight`). `EReal` evaluates `⊤ + ⊥ = ⊥` and `0 · (±⊤) = 0`, values the book leaves
undefined; the side conditions in clauses 2, 4, 5 exclude exactly those undefined cases (without
them the clauses are false, e.g. `f₁ = √·`, `f₂ = −√·` at `0`, or `f = ∛·`, `g = (·)³` at `0`).
In clause 3 the undefined case evaluates to `⊥` on the right, where the inequality holds, so no
condition is stated. The book's functions are defined on `ℝ₊`; here they are functions `ℝ → ℝ`
evaluated at `t ≥ 0`, where only values on `[t, ∞)` enter, and continuity of `f` on `ℝ₊` is
`ContinuousOn f (Set.Ici 0)`. `g′` is `deriv g`, continuous differentiability is
`ContDiff ℝ 1 g`, "nondecreasing" is `Monotone g`. -/
theorem lemma_A_12 :
    (∀ (f : ℝ → ℝ) (t : ℝ), 0 ≤ t →
      diniLowerRight (fun s => -f s) t = -diniUpperRight f t) ∧
    (∀ (f₁ f₂ : ℝ → ℝ) (t : ℝ), 0 ≤ t →
      (diniUpperRight f₁ t ≠ ⊥ ∨ diniUpperRight f₂ t ≠ ⊤) →
      (diniUpperRight f₁ t ≠ ⊤ ∨ diniUpperRight f₂ t ≠ ⊥) →
      diniUpperRight (fun s => f₁ s + f₂ s) t ≤ diniUpperRight f₁ t + diniUpperRight f₂ t) ∧
    (∀ (f₁ f₂ : ℝ → ℝ) (t : ℝ), 0 ≤ t →
      diniLowerRight f₁ t + diniLowerRight f₂ t ≤ diniLowerRight (fun s => f₁ s + f₂ s) t) ∧
    (∀ (f g : ℝ → ℝ) (t : ℝ), 0 ≤ t → ContinuousOn f (Set.Ici 0) → ContDiff ℝ 1 g →
      Monotone g →
      (deriv g (f t) ≠ 0 ∨ (diniUpperRight f t ≠ ⊤ ∧ diniUpperRight f t ≠ ⊥)) →
      diniUpperRight (fun s => g (f s)) t = ((deriv g (f t) : ℝ) : EReal) * diniUpperRight f t) ∧
    (∀ (f g : ℝ → ℝ) (t : ℝ), 0 ≤ t → ContinuousOn f (Set.Ici 0) → ContDiff ℝ 1 g →
      Monotone g →
      (deriv g (f t) ≠ 0 ∨ (diniLowerRight f t ≠ ⊤ ∧ diniLowerRight f t ≠ ⊥)) →
      diniLowerRight (fun s => g (f s)) t = ((deriv g (f t) : ℝ) : EReal) * diniLowerRight f t) := by sorry

end ProcessingNetworks.PathCompact
