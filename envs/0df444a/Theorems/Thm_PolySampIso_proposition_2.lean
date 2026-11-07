-- Prove2me | Theorems.Thm_PolySampIso_proposition_2
-- name    : PolySampIso.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:28:26.891114+00:00
-- url     : https://prove2.me/theorems/5002c192-05bf-4812-b65e-fc58d5dc6933
-- title:
--   Algorithm 2 and Proposition 2, p.11 — the forwards step is exact and runs in time O(m(n + τ))
-- statement:
--   Let $X$ be a nonempty bounded polytope, $\rho$ the dual measure of Lemma 2, $\tau\in\mathbb N$ and $x\in X$. Draw $z^{(1)},\dots,z^{(\tau)}$ i.i.d. from $\mathrm{Exp}(s(x))=\bigotimes_j\mathrm{Exp}(s_j(x))$ and set $\gamma=\sum_l z^{(l)}$. Then:
--
--   1. $y=A^\top\gamma$ has law $T_x\big(\rho^{*\tau}\big)\propto e^{\langle x,\cdot\rangle}\rho^{*\tau}$, the forwards conditional (10) of the proximal sampler;
--   2. there is a program for the real RAM with Gaussian and exponential samples which, on input $x$, $A$, $b$ and $\tau$, halts on every realization of its randomness after at most $C\,m(n+\tau)$ operations ($C$ a universal constant) and outputs a point with exactly this law.
--
--   So the forwards step of Algorithm 1 for the log barrier is implemented exactly and cheaply; all the difficulty of the sampler sits in the backwards step.
--
--   Differences from the source:
--   - encoding: z(i) ∼ i.i.d. Exp(s(x)) over ℝ^m_{>0} → the product Lebesgue density ∏_{l,j} s_j(x)e^{−s_j(x)z_{l,j}}𝕀_{z_{l,j}≥0}; reason: footnote 6: ℝ>0 versus ℝ≥0 is a null set
--   - encoding: distributed as (10), Tₓ exp(−φ∗τ) → the tilt Tₓ of the τ-fold convolution of the measure ρ of Lemma 2; reason: the density exp(−φ∗τ) is the measure ρ^{∗τ}
--   - reading: can be computed in time O(m(n + τ)) (in the real RAM of §2.1) → ∃ one Admissible program of PolySampIso.Machine and C > 0, before all inputs: on every pair of random streams it halts with work ≤ C·m(n+τ), its output map is measurable, and its output law is the law of A⊤γ; reason: the paper names the model without an instruction list; the program must sample the stated law exactly
--   - encoding: τ ∈ N → τ ≥ 1; reason: the paper's N starts at 1 ([n] := {i ∈ N | i ≤ n})
--   - encoding: the standing assumption of §2.3 (a nonempty, full-dimensional, bounded polytope; A full-rank) → X = {Ax < b} nonempty and bounded, n ≥ 1; reason: X is open, so nonempty means full-dimensional; nonempty and bounded imply full column rank
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), Algorithm 2 and Proposition 2, p.11 (PDF p.13); (10), p.11

import Mathlib
import Definitions.Def_PolySampIso_Machine
import Definitions.Def_PolySampIso_LogBarrier
import Definitions.Def_PolySampIso_LLT
import Definitions.Def_PolySampIso_Forwards

open MeasureTheory ProbabilityTheory

namespace PolySampIso

/-- **Proposition 2** (exact forwards step, Algorithm 2).

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), Algorithm 2 and Proposition 2, p.11 (PDF p.13):

"Proposition 2. Let τ ∈ N and x ∈ X. Let z(i) ∼ i.i.d. Exp(s(x)) for all i ∈ [τ], and let
γ := Σi∈[τ] z(i). Then, y := A⊤γ is distributed as (10) and can be computed in time O(m(n + τ))."
(10), p.11: "πY|X=x τ = Tx exp (−φ∗τ) ∝ exp (⟨x, ·⟩ − φ∗τ(·))."

**Formalization Note.**
1. The law clause: `forwardsLaw A b τ x`, the law of `A⊤Σ_{l<τ} z^{(l)}` with `z^{(l)}` i.i.d.
   `Exp(s(x)) = ⊗ⱼ Exp(sⱼ(x))`, equals the tilt `T_x(ρ^{∗τ})` of the `τ`-fold convolution of the
   dual measure `ρ = exp(−φ)` of Lemma 2.
2. The time clause, in the machine `PolySampIso.Machine`: one `Admissible` program and one
   constant `C`, chosen before all inputs; the input is `x` in the `x₀` slot of `inputState`
   (scalar cells `0`) and `τ` as the first tail scalar. On every pair of streams it halts with
   work `≤ C·m(n + τ)`, its output map is measurable, and its output law is `forwardsLaw A b τ x`.
`τ ∈ N` is `τ ≥ 1` (the paper's `N` starts at 1). The standing assumption of §2.3 is kept. -/
theorem proposition_2 :
    (∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ), StandingAssumption A b →
      0 < n → ∀ τ : ℕ, 1 ≤ τ → ∀ x ∈ polytope A b,
        forwardsLaw A b τ x = tilt x (convPow (dualMeasure A b) τ)) ∧
    ∃ P : Program, Admissible P ∧ ∃ C : ℝ, 0 < C ∧
      ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ), StandingAssumption A b →
        0 < n → ∀ τ : ℕ, 1 ≤ τ → ∀ x ∈ polytope A b,
          let s₀ := inputState ![0, 0, 0] x A b [(τ : ℝ)]
          (∀ ωs : Streams, ∃ k, (run P s₀ ωs k).halted = true ∧
            ((run P s₀ ωs k).work : ℝ) ≤ C * m * (n + τ)) ∧
          Measurable (finalOutput n P s₀) ∧
          tape.map (finalOutput n P s₀) = forwardsLaw A b τ x := by sorry

end PolySampIso
