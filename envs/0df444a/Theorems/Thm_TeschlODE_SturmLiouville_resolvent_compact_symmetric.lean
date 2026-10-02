-- Prove2me | Theorems.Thm_TeschlODE_SturmLiouville_resolvent_compact_symmetric
-- name    : TeschlODE.SturmLiouville.resolvent_compact_symmetric
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T11:27:30.016802+00:00
-- url     : https://prove2.me/theorems/2416d7b0-39dc-49f2-8664-4f93da238a41
-- title:
--   Lemma 5.10 — the resolvent R_L(z) is compact, and symmetric for real z
-- statement:
--   Assume (5.45), fix $z \in \mathbb{C}$, and let $u_a$, $u_b$ solve $L u = z u$ on $[a,b]$ with the initial conditions (5.62) and $W(z) = W(u_b, u_a) \ne 0$. Let $R_L(z)$ be the resolvent (5.64) built from the Green function (5.65). Then:
--
--   1. $R_L(z)$ is compact on $H_0 = C([a,b], \mathbb{C})$ with the scalar product (5.52): for every sequence $g_n \in H_0$ with $\sup_n \|g_n\| < \infty$ there are a subsequence $g_{n_k}$ and $h \in H_0$ with
--   $$\| R_L(z) g_{n_k} - h \| \to 0 ;$$
--   2. if $z \in \mathbb{R}$, $R_L(z)$ is symmetric: $\langle g, R_L(z) f\rangle = \langle R_L(z) g, f\rangle$ for all $f, g \in H_0$.
--
--   Together with $\operatorname{Ran}(R_L(z)) = D(L)$ this is what allows the spectral theorem for compact symmetric operators to be applied to the unbounded operator $L$.
--
--   **Formalization Note.** Elements of $H_0$ are functions continuous on $[a,b]$; the limit $h$ is required to be continuous on $[a,b]$, i.e. to lie in $H_0$, not in its completion. Boundedness is $\exists C, \forall n, \|g_n\|^2 \le C$ and convergence is $\|R_L(z)g_{n_k} - h\|^2 \to 0$, with $\|f\|^2 = \operatorname{Re}\langle f, f\rangle$. The hypothesis $W(z) \ne 0$ rules out the junk resolvent $0$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 159, Lemma 5.10

import Mathlib
import Definitions.Def_TeschlODE_SturmLiouville_RegularSL
import Definitions.Def_TeschlODE_SturmLiouville_SLOp
import Definitions.Def_TeschlODE_SturmLiouville_SLInner
import Definitions.Def_TeschlODE_SturmLiouville_SLWronskian
import Definitions.Def_TeschlODE_SturmLiouville_SLResolvent

namespace TeschlODE.SturmLiouville

/-- Teschl, Lemma 5.10, p. 159: under (5.45), fix `z ∈ ℂ` and let `ua`, `ub` solve `L u = z u` on
`[a, b]` with the initial conditions (5.62), with `W(z) = W(u_b, u_a) ≠ 0`. Then the resolvent
`R_L(z)` (5.64) is compact on `H₀ = C([a, b], ℂ)` with the scalar product (5.52): every sequence
`gₙ ∈ H₀` bounded in the `H₀`-norm has a subsequence along which `R_L(z) gₙ` converges in the
`H₀`-norm to some `h ∈ H₀`. In addition, for real `z` it is symmetric:
`⟨g, R_L(z) f⟩ = ⟨R_L(z) g, f⟩` for `f, g ∈ H₀`. -/
theorem resolvent_compact_symmetric {p q r : ℝ → ℝ} {a b α β : ℝ}
    (hreg : RegularSL p q r a b) (z : ℂ) (ua ub : ℝ → ℂ)
    (hua : ContDiffOn ℝ 2 ua (Set.Icc a b))
    (hua_eq : ∀ x ∈ Set.Icc a b, SLOp p q r a b ua x = z * ua x)
    (hua_a : ua a = (Real.sin α : ℂ))
    (hua_a' : (p a : ℂ) * derivWithin ua (Set.Icc a b) a = (Real.cos α : ℂ))
    (hub : ContDiffOn ℝ 2 ub (Set.Icc a b))
    (hub_eq : ∀ x ∈ Set.Icc a b, SLOp p q r a b ub x = z * ub x)
    (hub_b : ub b = (Real.sin β : ℂ))
    (hub_b' : (p b : ℂ) * derivWithin ub (Set.Icc a b) b = (Real.cos β : ℂ))
    (hW : SLWronskian p a b ub ua a ≠ 0) :
    (∀ g : ℕ → ℝ → ℂ, (∀ n, ContinuousOn (g n) (Set.Icc a b)) →
      (∃ C : ℝ, ∀ n, (SLInner r a b (g n) (g n)).re ≤ C) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ h : ℝ → ℂ, ContinuousOn h (Set.Icc a b) ∧
        Filter.Tendsto
          (fun n => (SLInner r a b (SLResolvent p r a b ua ub (g (φ n)) - h)
            (SLResolvent p r a b ua ub (g (φ n)) - h)).re) Filter.atTop (nhds 0)) ∧
    (z.im = 0 → ∀ f g : ℝ → ℂ, ContinuousOn f (Set.Icc a b) → ContinuousOn g (Set.Icc a b) →
      SLInner r a b g (SLResolvent p r a b ua ub f) =
        SLInner r a b (SLResolvent p r a b ua ub g) f) := by sorry

end TeschlODE.SturmLiouville
