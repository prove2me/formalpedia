-- Prove2me | Theorems.Thm_QubitFreqSensing_lemma_A_1
-- name    : QubitFreqSensing.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:00.323264+00:00
-- url     : https://prove2.me/theorems/20ace477-a6b1-48e4-8fee-309a9e9ef47c
-- title:
--   Lemma A.1 — $J$ is weakly upper semicontinuous on $K$
-- statement:
--   Let $N\ge1$, $\omega_1,\dots,\omega_N>0$ and $C>0$. Extend $J$ from (13) to $K=\{v:|v|\le1\text{ a.e. on }[0,2\pi]\}$ with $\log0=-\infty$. Let $f_n,f\in K$ and suppose $f_n\to f$ weakly, in the sense that $\langle h,f_n\rangle\to\langle h,f\rangle$ for every $h\in L^2([0,2\pi];\mathbb C)$. Then
--
--   $$
--   J(f)\ \ge\ \limsup_{n\to\infty}J(f_n).
--   $$
--
--   Together with the weak sequential compactness of $K$ this gives the existence of a maximizer of $J$ (Lemma 5.7).
--
--   Differences from the source:
--   - encoding: K = {v ∈ L²([0, 2π]; ℂ) : |v(x)| ≤ 1 a.e.} → a.e.-strongly measurable v on [0, 2π] with ‖v‖ ≤ 1 a.e. (closedDiscFns); reason: the same L² classes
--   - encoding: for any h ∈ L²([0, 2π]; ℂ), ⟨h, f_n⟩ → ⟨h, f⟩ → ∀ h with MemLp h 2 on [0, 2π], Tendsto (inner2pi h (f n)) to inner2pi h f; reason: Mathlib's L² membership
--   - encoding: J : 𝕋 → ℝ ∪ {−∞} with log 0 = −∞ → J valued in EReal, penalty via a lower Lebesgue integral; reason: Lean's Real.log 0 = 0 and non-integrable Bochner integrals = 0 would hide −∞
-- source:
--   Chen, Coladangelo, Li, Zhang, Sensing frequencies at the discrete Grover-Heisenberg limit using a single qubit, manuscript (STOC 2027 submission; held version sha256 fd015276…c95c9a2), Lemma A.1, p.33 (PDF p.33), with the definitions of K and weak convergence on the same page

import Mathlib
import Definitions.Def_QubitFreqSensing_Potential

open MeasureTheory Filter Topology Real

namespace QubitFreqSensing

/-- **Lemma A.1** (weak upper semicontinuity of `J`; Chen, Coladangelo, Li, Zhang, manuscript (STOC
2027 submission), Lemma A.1, p.33). On `K = {v ∈ L²([0, 2π]; ℂ) : |v(x)| ≤ 1 a.e.}`, with `J` defined
by (13) and `log 0 = −∞`, and "(fn) in K weakly converges to f ∈ K if for any h ∈ L2([0, 2π]; C), we
have ⟨h, fn⟩ → ⟨h, f⟩": "Suppose (fn) weakly converges to f. Then, we have J(f) ≥ lim sup_{n→∞}
J(fn)."

**Formalization Note** `K` is `closedDiscFns`; `h ∈ L²` is `MemLp h 2` for Lebesgue measure on
`[0, 2π]`; the `lim sup` is taken in `EReal`. The standing assumptions of §5 (`N ≥ 1`, `ω_i > 0`)
and `C > 0` (p.18) are hypotheses. -/
theorem lemma_A_1 (N : ℕ) (hN : 1 ≤ N) (ω : Fin N → ℝ) (hω : ∀ i, 0 < ω i)
    (C : ℝ) (hC : 0 < C) (f : ℕ → ℝ → ℂ) (g : ℝ → ℂ)
    (hf : ∀ n, f n ∈ closedDiscFns) (hg : g ∈ closedDiscFns)
    (hweak : ∀ h : ℝ → ℂ, MemLp h 2 (volume.restrict (Set.Icc 0 (2 * π))) →
      Tendsto (fun n => inner2pi h (f n)) atTop (𝓝 (inner2pi h g))) :
    limsup (fun n => J C ω (f n)) atTop ≤ J C ω g := by sorry

end QubitFreqSensing
