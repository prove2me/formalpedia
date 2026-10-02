-- Prove2me | Theorems.Thm_TeschlQM_SturmLiouville_selfAdjoint_bc
-- name    : TeschlQM.SturmLiouville.selfAdjoint_bc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:48:20.452844+00:00
-- url     : https://prove2.me/theorems/3ef4b8af-7494-4066-a1aa-7d03f12c273d
-- title:
--   Theorem 9.6 — self-adjoint realizations with separated boundary conditions
-- statement:
--   Let $(a,b,p,q,r)$ be Sturm–Liouville data. If $\tau$ is l.c. at $a$, let $v \in \mathfrak{D}(\tau)$ with $W_a(v^*, v) = 0$ and $W_a(v, f) \neq 0$ for some $f \in \mathfrak{D}(\tau)$; similarly, if $\tau$ is l.c. at $b$, let $w$ be an analogous function at $b$. Then the operator
--   $$A : \mathfrak{D}(A) \to L^2(I, r\,dx), \quad f \mapsto \tau f, \qquad \mathfrak{D}(A) = \{ f \in \mathfrak{D}(\tau) \mid W_a(v, f) = 0 \text{ if l.c. at } a,\ W_b(w, f) = 0 \text{ if l.c. at } b\}$$
--   is self-adjoint. Moreover the set $\mathfrak{D}_1$ of (9.21) is a core for $A$: the closure of the restriction of $A$ to $\mathfrak{D}_1$ is $A$.
--
--   This produces the self-adjoint Sturm–Liouville operators whose resolvents and spectra are studied in the rest of the chapter.
--
--   **Formalization Note.** The conclusion asserts that there is a `LinearPMap` $A$ on $L^2(I, r\,dx)$ whose graph is $\{(f, \tau f) \mid f \in \mathfrak{D}(A)\}$ (so $A$ is well defined), that $A$ is self-adjoint (Mathlib's `IsSelfAdjoint`), and that the operator $A_1$ with graph $\{(f, \tau f) \mid f \in \mathfrak{D}_1\}$ exists and has closure $A$. When $\tau$ is l.p. at an endpoint the hypothesis on $v$ (resp. $w$) is vacuous and no condition is imposed there.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 187, Theorem 9.6, Eqs. (9.19)–(9.21)

import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_operatorGraph

namespace TeschlQM.SturmLiouville

open MeasureTheory

/-- Teschl, Theorem 9.6, p. 187. If `τ` is l.c. at `a`, let `v ∈ D(τ)` with `W_a(v*, v) = 0` and
`W_a(v, f) ≠ 0` for some `f ∈ D(τ)`; similarly `w` at `b` if `τ` is l.c. at `b`. Then
`f ↦ τ f` on `𝔇(A)` (9.20) is a (well-defined) self-adjoint operator `A` in `L²(I, r dx)`, and
`D₁` (9.21) is a core for `A`: the closure of `A` restricted to `D₁` is `A`. -/
theorem selfAdjoint_bc (L : SLData) (v w : ℝ → ℂ)
    (hv : IsLimitCircleLeft L → InMaxDomain L v ∧
      wronskianLeft L (fun x => starRingEnd ℂ (v x)) v = 0 ∧
      ∃ f : ℝ → ℂ, InMaxDomain L f ∧ wronskianLeft L v f ≠ 0)
    (hw : IsLimitCircleRight L → InMaxDomain L w ∧
      wronskianRight L (fun x => starRingEnd ℂ (w x)) w = 0 ∧
      ∃ f : ℝ → ℂ, InMaxDomain L f ∧ wronskianRight L w f ≠ 0) :
    ∃ A : Lp ℂ 2 L.measure →ₗ.[ℂ] Lp ℂ 2 L.measure,
      (A.graph : Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure)) =
          operatorGraph L (bcDomain L v w) ∧
        IsSelfAdjoint A ∧
        ∃ A₁ : Lp ℂ 2 L.measure →ₗ.[ℂ] Lp ℂ 2 L.measure,
          (A₁.graph : Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure)) =
              operatorGraph L (coreDomain L v w) ∧
            A₁.closure = A := by sorry

end TeschlQM.SturmLiouville
