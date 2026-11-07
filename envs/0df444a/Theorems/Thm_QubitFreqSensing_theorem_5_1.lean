-- Prove2me | Theorems.Thm_QubitFreqSensing_theorem_5_1
-- name    : QubitFreqSensing.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:22:41.394414+00:00
-- url     : https://prove2.me/theorems/da4bf04d-3db1-4fdf-acc2-90b516614684
-- title:
--   Theorem 5.1 — simultaneous correlation: some $u\in\mathbb T$ has $|\int_0^{2\pi}u(x)\cos(\omega_i x)\,dx|\ge c/\sqrt N$ for all $i$
-- statement:
--   There is a universal constant $c>0$ such that for every integer $N\ge1$ and all $\omega_1,\dots,\omega_N>0$ there is a measurable function $u$ with $|u(x)|<1$ for all $x\in[0,2\pi]$ (that is, $u\in\mathbb T$) such that
--
--   $$
--   \left|\int_0^{2\pi}u(x)\cos(\omega_i x)\,dx\right|\ \ge\ \frac{c}{\sqrt N}\qquad(i=1,\dots,N).
--   $$
--
--   The frequencies are arbitrary positive reals: they need not be distinct, separated or integral. This is the paper's main technical result. After the change of variables $s=2\pi t/T$ and a rounding step it gives the two pulse patterns of Theorem 5.13, and hence the $O(\sqrt N/B_{\min})$ sensing time.
--
--   Differences from the source:
--   - encoding: 𝕋 = L² functions [0, 2π] → 𝔻 → measurable u : ℝ → ℂ with ‖u x‖ < 1 on [0, 2π] (discFns); reason: every quantity depends only on the a.e. class; L² is automatic for |u| < 1
-- source:
--   Chen, Coladangelo, Li, Zhang, Sensing frequencies at the discrete Grover-Heisenberg limit using a single qubit, manuscript (STOC 2027 submission; held version sha256 fd015276…c95c9a2), Theorem 5.1, p.16 (PDF p.16)

import Mathlib
import Definitions.Def_QubitFreqSensing_Potential

open Real

namespace QubitFreqSensing

/-- **Theorem 5.1** (simultaneous correlation; Chen, Coladangelo, Li, Zhang, manuscript (STOC 2027
submission), Theorem 5.1, p.16). "There exists a universal constant c > 0 so that for every integer
N ≥ 1 and any ω1, . . . , ωN > 0, there is a function u ∈ 𝕋 such that, for all i = 1, . . . , N, we
have |∫_0^{2π} u(x) cos(ωix)dx| ≥ c/√N."

**Formalization Note** `𝕋` is `discFns` (measurable, `|u| < 1` on `[0, 2π]`). The frequencies are
arbitrary positive reals: not distinct, separated or integral. `c` is chosen before `N` and `ω`. -/
theorem theorem_5_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ), 1 ≤ N → ∀ ω : Fin N → ℝ, (∀ i, 0 < ω i) →
      ∃ u ∈ discFns, ∀ i,
        c / Real.sqrt N ≤ ‖∫ x in (0 : ℝ)..2 * π, u x * (Real.cos (ω i * x) : ℂ)‖ := by sorry

end QubitFreqSensing
