-- Prove2me | Theorems.Thm_TeschlODE_SturmLiouville_rayleigh_ritz
-- name    : TeschlODE.SturmLiouville.rayleigh_ritz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T11:47:54.781684+00:00
-- url     : https://prove2.me/theorems/e96401e8-df6a-49ed-889c-23eff560500d
-- title:
--   Lemma 5.12 — eigenvalues bounded below, ordered E₀ < E₁ < ⋯, Rayleigh–Ritz principle
-- statement:
--   Assume (5.45) and fix $\alpha, \beta$. The eigenvalues of the regular Sturm–Liouville problem are bounded from below and can be ordered as
--   $$E_0 < E_1 < \cdots . \qquad (5.75)$$
--   Moreover the **Rayleigh–Ritz principle** holds:
--   $$E_0 = \min_{f \in D(L),\ \|f\| = 1} Q(f) = \min_{f \in D(L),\ \|f\| = 1} \langle f, L f\rangle, \qquad (5.76)$$
--   with equality if and only if $f = u_0$. In particular, for $0 \le \alpha \le \frac{\pi}{2}$ and $\frac{\pi}{2} \le \beta \le \pi$,
--   $$\min_{x \in [a,b]} q(x) \le E_0 . \qquad (5.77)$$
--
--   Here $Q$ is the quadratic form (5.71). The lemma is the variational characterisation of the ground state; it is the starting point of comparison and oscillation arguments later in the chapter.
--
--   **Formalization Note.** (5.75) is stated as: there is a strictly increasing $E : \mathbb{N} \to \mathbb{R}$ whose values are exactly the eigenvalues of $L$ (so they are bounded below by $E_0$). Each minimum in (5.76) is `IsLeast` of the set of values $\operatorname{Re} Q(f)$, respectively $\operatorname{Re}\langle f, Lf\rangle$, over normalized $f \in D(L)$ (both are real on $D(L)$), so attainment is part of the claim. "Equality iff $f = u_0$" is read as: a normalized $f \in D(L)$ has $\langle f, Lf\rangle = E_0$ iff $Lf = E_0 f$ on $[a,b]$; since $E_0$ is simple, this means $f = c\,u_0$ with $|c| = 1$ — the book's literal "$f = u_0$" holds only up to such a unimodular factor. $\min_{[a,b]} q \le E_0$ is written $\exists x \in [a,b],\ q(x) \le E_0$ (the minimum of the continuous $q$ is attained). The book leaves the case of negative boundary terms "as an exercise"; the statement covers all $\alpha, \beta$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 162, Lemma 5.12

import Mathlib
import Definitions.Def_TeschlODE_SturmLiouville_RegularSL
import Definitions.Def_TeschlODE_SturmLiouville_SLOp
import Definitions.Def_TeschlODE_SturmLiouville_SLDomain
import Definitions.Def_TeschlODE_SturmLiouville_IsSLEigenfunction
import Definitions.Def_TeschlODE_SturmLiouville_SLInner
import Definitions.Def_TeschlODE_SturmLiouville_SLQuadForm

namespace TeschlODE.SturmLiouville

/-- Teschl, Lemma 5.12, p. 162: under (5.45), the eigenvalues of the regular Sturm–Liouville
problem are bounded from below and can be ordered `E₀ < E₁ < ⋯` (5.75), i.e. they are the values
of a strictly increasing sequence. Rayleigh–Ritz principle (5.76): `E₀` is the minimum of `Q(f)`
and of `⟨f, L f⟩` over `f ∈ D(L)` with `‖f‖ = 1`, and a normalized `f ∈ D(L)` attains it iff
`f` is an eigenfunction for `E₀` (i.e. `f` is `u₀` up to a unimodular factor). Finally (5.77):
if `0 ≤ α ≤ π/2` and `π/2 ≤ β ≤ π`, then `min_{[a,b]} q ≤ E₀`. -/
theorem rayleigh_ritz {p q r : ℝ → ℝ} {a b : ℝ} (α β : ℝ) (hreg : RegularSL p q r a b) :
    ∃ E : ℕ → ℝ, StrictMono E ∧
      (∀ z : ℂ, (∃ f : ℝ → ℂ, IsSLEigenfunction p q r a b α β z f) ↔ ∃ n, z = (E n : ℂ)) ∧
      IsLeast {x : ℝ | ∃ f : ℝ → ℂ, SLDomain p a b α β f ∧ (SLInner r a b f f).re = 1 ∧
        x = (SLQuadForm p q a b α β f f).re} (E 0) ∧
      IsLeast {x : ℝ | ∃ f : ℝ → ℂ, SLDomain p a b α β f ∧ (SLInner r a b f f).re = 1 ∧
        x = (SLInner r a b f (SLOp p q r a b f)).re} (E 0) ∧
      (∀ f : ℝ → ℂ, SLDomain p a b α β f → (SLInner r a b f f).re = 1 →
        ((SLInner r a b f (SLOp p q r a b f)).re = E 0 ↔
          ∀ x ∈ Set.Icc a b, SLOp p q r a b f x = (E 0 : ℂ) * f x)) ∧
      (0 ≤ α → α ≤ Real.pi / 2 → Real.pi / 2 ≤ β → β ≤ Real.pi →
        ∃ x ∈ Set.Icc a b, q x ≤ E 0) := by sorry

end TeschlODE.SturmLiouville
