-- Prove2me | Theorems.Thm_PolyEulerFlow_lemma_28
-- name    : PolyEulerFlow.lemma_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:21:37.030198+00:00
-- url     : https://prove2.me/theorems/39a2060d-08ea-4f17-a1be-46e383055d82
-- title:
--   Lemma 28 — the coupled scalar box (25) is invariant
-- statement:
--   Consider the compiled field $F$ of §6.3 of a separated affine program at scale $h>0$, with $\varepsilon=h^K$. There is $\varepsilon_0>0$ such that, whenever $0<\varepsilon\le\varepsilon_0$, $0\le\nu\le\varepsilon^2$, $0<\eta\le1$ and $\|\xi\|_\infty\le\nu$, one step $Z^+=Z+\eta F(Z)+\eta\xi$ of the scheme (21) from a state $Z$ at which every test satisfies $|u_j(Y,h)|\le1$ maps the scalar box
--   $$-\nu\le p_i\le1+\nu,\qquad\varepsilon/2\le\tau_i\le1+3\nu,\qquad|v_j|\le1+4\nu\tag{25}$$
--   into itself; and for the exact scheme ($\nu=0$) it maps the sharper box $p_i\in[0,1]$, $\tau_i\in[\varepsilon,1]$, $v_j\in[-1,1]$ into itself.
--
--   This is the a priori bound on the scalar coordinates (gates, timers, comparators) used by every later estimate.
--
--   Differences from the source:
--   - reading: the scheme (21) preserves (25), for sufficiently small ε → ∃ ε₀ > 0 (depending on the program and K); one step of (21) with any η ∈ (0, 1] and ‖ξ‖∞ ≤ ν ≤ ε² maps (25) into (25); reason: invariance of a set under a scheme is invariance under each of its steps; p.27 lets constants depend on the fixed program
--   - reading: Assume |u_j(Y, h)| ≤ 1 → |u_j(Y, h)| ≤ 1 at the current state; reason: the assumption concerns the state the step starts from
--   - generalization: h = 2^{−s}, ε = h^K with K ≥ 256 → every real h > 0 and every K ∈ ℕ with h^K ≤ ε₀; reason: the dyadic scales and K ≥ 256 are among them
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), Lemma 28, p.28 (PDF 30)

import Mathlib
import Definitions.Def_PolyEulerFlow_IsUniformClock

namespace PolyEulerFlow

/-- **Lemma 28 (Coupled scalar box)**, p.28 (PDF 30). Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript,
sha256 c4e01b2b…).

For the compiled field of a separated affine program at scale `h`, with `ε = h^K`: for sufficiently small `ε`, one step
`Z⁺ = Z + ηF(Z) + ηξ` of the scheme (21), with `0 < η ≤ 1`, `‖ξ‖∞ ≤ ν ≤ ε²`, maps a state in the scalar box (25)
`-ν ≤ p_i ≤ 1 + ν`, `ε/2 ≤ τ_i ≤ 1 + 3ν`, `|v_j| ≤ 1 + 4ν`, at which all tests satisfy `|u_j(Y, h)| ≤ 1`, to a state in (25). For the
exact scheme (`ν = 0`) the sharper box `p_i ∈ [0, 1]`, `τ_i ∈ [ε, 1]`, `v_j ∈ [-1, 1]` is preserved in the same way.

**Formalization Note** "Preserves" is read as invariance under one step of (21), for every step size and disturbance allowed by (21);
"sufficiently small" is an `ε₀ > 0`, which may depend on the fixed program (p.27). The hypothesis `|u_j(Y, h)| ≤ 1` is imposed at the current
state. -/
theorem lemma_28 {m g : ℕ} (prog : SeparatedAffineProgram m g) (K : ℕ) :
    ∃ ε0 : ℝ, 0 < ε0 ∧
      ∀ (h ν η : ℝ) (ξ Z : CompiledState m g),
        0 < h → h ^ K ≤ ε0 → 0 ≤ ν → ν ≤ (h ^ K) ^ 2 → 0 < η → η ≤ 1 → ‖ξ‖ ≤ ν →
        (∀ j, |prog.test j (dataY Z) h| ≤ 1) →
        let ε := h ^ K
        let Z' := Z + η • compiledField prog K h Z + η • ξ
        (scalarBox ε ν Z → scalarBox ε ν Z') ∧
        (ν = 0 →
          (∀ i, 0 ≤ phaseBit i Z ∧ phaseBit i Z ≤ 1 ∧ ε ≤ Z (.inl (.inr i)) ∧ Z (.inl (.inr i)) ≤ 1) →
          (∀ j, |compV Z j| ≤ 1) →
          (∀ i, 0 ≤ phaseBit i Z' ∧ phaseBit i Z' ≤ 1 ∧ ε ≤ Z' (.inl (.inr i)) ∧ Z' (.inl (.inr i)) ≤ 1) ∧
          (∀ j, |compV Z' j| ≤ 1)) := by sorry

end PolyEulerFlow
