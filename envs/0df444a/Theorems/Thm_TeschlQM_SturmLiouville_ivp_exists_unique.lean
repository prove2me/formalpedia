-- Prove2me | Theorems.Thm_TeschlQM_SturmLiouville_ivp_exists_unique
-- name    : TeschlQM.SturmLiouville.ivp_exists_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:46:05.700864+00:00
-- url     : https://prove2.me/theorems/02f8416e-6dda-46be-9182-9c8304a1b02e
-- title:
--   Theorem 9.1 — existence and uniqueness for the initial value problem
-- statement:
--   Let $(a,b,p,q,r)$ be Sturm–Liouville data, and let $g$ be a function with $rg \in L^1_{loc}(I)$. Fix $c \in I$ and $\alpha, \beta \in \mathbb{C}$. Then for every $z \in \mathbb{C}$ there is a unique solution $f = f_z$ with $f, pf' \in AC_{loc}(I)$ of
--   $$(\tau - z) f = g, \qquad f(c) = \alpha,\quad (pf')(c) = \beta,$$
--   and for every $x \in I$ the map $z \mapsto f_z(x)$ is entire.
--
--   This is the basic existence theorem for Sturm–Liouville equations with merely locally integrable coefficients, where the classical Picard–Lindelöf theorem does not apply.
--
--   **Formalization Note.** The solutions form a family $F(z, \cdot)$. Uniqueness is stated on $I$ (values outside $I$ are irrelevant); since the quasi-derivative is determined by $f$ on $I$, it covers the pair $(f, pf')$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 182, Theorem 9.1

import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_SolvesTau

namespace TeschlQM.SturmLiouville

open MeasureTheory

/-- Teschl, Theorem 9.1, p. 182. Suppose `r g ∈ L¹_loc(I)`. Then for every `z ∈ ℂ` there is a
unique solution `f, p f′ ∈ AC_loc(I)` of `(τ − z) f = g` (9.8) with `f(c) = α`, `(p f′)(c) = β`
(9.9), and `f` is entire in `z`. The solutions are given as a family `F z`; uniqueness is on `I`
(values outside `I` are irrelevant), and uniqueness of `p f′` on `I` follows from that of `f`. -/
theorem ivp_exists_unique (L : SLData) (g : ℝ → ℂ)
    (hg : LocallyIntegrableOn (fun x => (L.r x : ℂ) * g x) L.I)
    (c : ℝ) (hc : c ∈ L.I) (α β : ℂ) :
    ∃ F : ℂ → ℝ → ℂ,
      (∀ z : ℂ, IsSolution L z g (F z) ∧ F z c = α ∧ quasiDeriv L (F z) c = β) ∧
      (∀ (z : ℂ) (f : ℝ → ℂ), IsSolution L z g f → f c = α → quasiDeriv L f c = β →
        ∀ x ∈ L.I, f x = F z x) ∧
      (∀ x ∈ L.I, Differentiable ℂ (fun z => F z x)) := by sorry

end TeschlQM.SturmLiouville
