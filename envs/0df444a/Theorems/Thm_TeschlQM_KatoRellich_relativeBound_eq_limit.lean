-- Prove2me | Theorems.Thm_TeschlQM_KatoRellich_relativeBound_eq_limit
-- name    : TeschlQM.KatoRellich.relativeBound_eq_limit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T22:22:58.890534+00:00
-- url     : https://prove2.me/theorems/7e46b2f9-ed32-41d7-955f-034b6940f26b
-- title:
--   Lemma 6.3 — the A-bound as a limit of resolvent norms
-- statement:
--   Let $A$ be a self-adjoint operator and $B$ an $A$ bounded operator in a complex Hilbert space $\mathfrak{H}$. Then the $A$-bound of $B$ is
--   $$\lim_{\lambda \to \infty} \|BR_A(\pm i\lambda)\|, \tag{6.2}$$
--   for each choice of sign. If $A$ is bounded from below (by some $\gamma \in \mathbb{R}$), then also
--   $$\text{$A$-bound of } B = \lim_{\lambda \to \infty} \|BR_A(-\lambda)\|.$$
--
--   This formula is what gives $\|BR_A(\pm i\lambda)\| < 1$ for large $\lambda$ when the $A$-bound is less than one.
--
--   **Formalization Note.** The limits are taken in $[0,\infty]$ along $\lambda \to +\infty$ in $\mathbb{R}$; only eventual values matter, and for $\lambda > 0$ (resp. $\lambda$ large) the points $\pm i\lambda$ (resp. $-\lambda$) lie in $\rho(A)$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 134, Lemma 6.3, Eq. (6.2)

import Mathlib
import Definitions.Def_TeschlQM_KatoRellich_IsRelativelyBounded
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
import Definitions.Def_TeschlQM_KatoRellich_resolvent
import Definitions.Def_TeschlQM_KatoRellich_compCLM
import Definitions.Def_TeschlQM_KatoRellich_opNorm

namespace TeschlQM.KatoRellich

open scoped ENNReal
open Filter Topology Complex

/-- Teschl, Lemma 6.3 and (6.2), p. 134. If `A` is self-adjoint and `B` is `A` bounded, the
`A`-bound of `B` is `lim_{λ→∞} ‖BR_A(±iλ)‖` (both signs). If `A` is bounded from below, `±iλ`
may be replaced by `-λ`. -/
theorem relativeBound_eq_limit {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A B : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (hB : IsRelativelyBounded A B) :
    Tendsto (fun t : ℝ => opNorm (compCLM B (resolvent A ((t : ℂ) * I)))) atTop
        (𝓝 (relativeBound A B)) ∧
      Tendsto (fun t : ℝ => opNorm (compCLM B (resolvent A (-((t : ℂ) * I))))) atTop
        (𝓝 (relativeBound A B)) ∧
      ∀ γ : ℝ, TeschlQM.Shared.IsBoundedBelowBy A γ →
        Tendsto (fun t : ℝ => opNorm (compCLM B (resolvent A (-(t : ℂ))))) atTop
          (𝓝 (relativeBound A B)) := by sorry

end TeschlQM.KatoRellich
