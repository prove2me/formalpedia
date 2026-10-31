-- Prove2me | Theorems.Thm_StrategicObfuscation_obfuscation_equilibria
-- name    : StrategicObfuscation.obfuscation_equilibria
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:52:05.79939+00:00
-- url     : https://prove2.me/theorems/ae3f3369-8692-406c-a1eb-ec024eb38f2e
-- title:
--   Proof of Proposition 1, b.1–b.2, pp.27–28 — equilibria with obfuscation
-- statement:
--   Let $pV>c$.
--
--   1. For $\sigma\in[0,1]$ with $\sigma<\bar\sigma_2$, every equilibrium has $\alpha=1$, $e=e(1,\sigma)$ and $QV>c$, and an equilibrium with $\alpha=1$, $e=e(1,\sigma)$ exists.
--   2. For $\sigma\in[0,1]$ with $\sigma>\bar\sigma_2$ one has $f(\sigma)\le 0$.
--   3. For $\sigma\in[0,1)$ with $f(\sigma)\le 0$, every equilibrium has $QV=c$ and $\alpha>0$.
--   4. For $\sigma\in[0,1)$ with $f(\sigma)\le 0$, if $e(\cdot,\sigma)$ is continuous on $[0,1]$ and $\pi(\sigma,\cdot)$ is continuous on $[0,\infty)$, some $\alpha\in[0,1]$ solves (4), and $(e(\alpha,\sigma),\alpha,c/V)$ is an equilibrium.
--   5. If $f(\sigma)=0$, then $\alpha=1$ solves (4); at $\sigma=1$, $\alpha=0$ solves (4).
--
--   Above $\bar\sigma_2$ funding for sure would create too much obfuscation, so the sponsor randomizes.
--
--   **Formalization Note** At $\sigma=1$, $\alpha=0$ both sides of the cross-multiplied (4) are $0$. The value of the paper's function $\alpha(\sigma,p,g)$ at $\sigma=1$ is a boundary statement only: other $\alpha$ can solve (4) there.
--
--   Differences from the source:
--   - generalization: Assumption 1 with ∂²π/∂σ∂e < 0 for a twice differentiable π → IsDetection: monotonicity plus decreasing differences in σ, strict whenever π(σ,·) separates the two efforts; reason: the C² class satisfies it by integrating the mixed partial, and the paper's own example on p.14, which the strict form excludes, also satisfies it
--   - encoding: e(α, σ) written as a function → a fixed selection E with IsEffort π g E; reason: the argmax in (1) may not be a singleton; every selection is covered and existence of a maximizer stays part of the hypothesis, as in (1)
--   - encoding: Bayes' rule (2) as a quotient → (2) cross-multiplied in IsEquilibrium; reason: the same equation whenever the denominator is nonzero; at σ = 1, e = 0 the report is off path and a PBE leaves Q free, where Lean's 0/0 = 0 would pin it
--   - encoding: (4) as a quotient equal to c/V → (4) cross-multiplied (SolvesFour); reason: the same equation whenever the denominator is nonzero; it keeps a meaning at σ = 1
--   - generalization: b.1 assumes σ ∈ (σ̄1, σ̄2) → σ < σ̄2; reason: the lower bound is not needed; the Lean statement specializes to the printed one
--   - reading: b.2 assumes σ ≥ σ̄2 → f(σ) ≤ 0, which holds for every σ > σ̄2 and at σ̄2 when f is continuous; reason: this is what the proof uses; without continuity of e(1,·) one can have f(σ̄2) > 0, and then no α solves (4) at σ̄2
--   - reading: b.2 "by continuity" → continuity of e(·,σ) and of π(σ,·) in the existence clause; reason: the paper's intermediate value step; it is not automatic, since effort can jump
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), proof of Proposition 1, b.1–b.2, pp.27–28

import Mathlib
import Definitions.Def_StrategicObfuscation_IsDetection
import Definitions.Def_StrategicObfuscation_IsEffort
import Definitions.Def_StrategicObfuscation_IsEquilibrium
import Definitions.Def_StrategicObfuscation_sigmaBarTwo
import Definitions.Def_StrategicObfuscation_SolvesFour

open Set

namespace StrategicObfuscation

/-- **Equilibria with obfuscation, steps b.1–b.2.**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), proof of Proposition 1, b.1–b.2, pp.27–28 (PDF pp.27–28).

Let `pV > c`.
* (b.1) For `σ < σ̄2`, every equilibrium has `α = 1`, `e = e(1, σ)`, `Q V > c`, and an equilibrium with
  `α = 1`, `e = e(1, σ)` exists.
* (b.2) For `σ < 1` with `f(σ) ≤ 0`, which holds for all `σ > σ̄2`, every equilibrium has `Q V = c` and
  `α > 0`. If `e(·, σ)` and `π(σ, ·)` are continuous, some `α ∈ [0, 1]` solves (4), and with `Q = c/V`
  it gives an equilibrium.
* At resources with `f(σ) = 0`, in particular at `σ̄2` for continuous `f`, `α = 1` solves (4); at
  `σ = 1`, `α = 0` solves (4).

**Formalization Note** The printed b.1 assumes `σ > σ̄1`, which is not needed. The printed b.2 reads
`σ ≥ σ̄2`; here the hypothesis is `f(σ) ≤ 0`, which is what the proof uses and what `σ ≥ σ̄2` means when
`f` is continuous. Without continuity of `e(1, ·)`, `f(σ̄2) > 0` is possible, and then no `α` solves
(4) at `σ̄2`. Continuity in the existence clause reads "by continuity". (4) is cross-multiplied, and
at `σ = 1`, `α = 0` it reads `0 = 0`. -/
theorem obfuscation_equilibria {V c g p : ℝ} {π : ℝ → ℝ → ℝ} {E : ℝ → ℝ → ℝ}
    (hc : 0 < c) (hcV : c < V) (hg : 0 < g) (hp1 : p ≤ 1)
    (hπ : IsDetection π) (hE : IsEffort π g E) (hpV : c < p * V) :
    (∀ σ ∈ Icc (0 : ℝ) 1, σ < sigmaBarTwo π V c p E →
      (∀ e α Q, IsEquilibrium π V c p E σ e α Q → α = 1 ∧ e = E 1 σ ∧ c < Q * V) ∧
      ∃ Q, IsEquilibrium π V c p E σ (E 1 σ) 1 Q) ∧
    (∀ σ ∈ Icc (0 : ℝ) 1, sigmaBarTwo π V c p E < σ → gap π V c p E σ ≤ 0) ∧
    (∀ σ ∈ Ico (0 : ℝ) 1, gap π V c p E σ ≤ 0 →
      ∀ e α Q, IsEquilibrium π V c p E σ e α Q → Q * V = c ∧ 0 < α) ∧
    (∀ σ ∈ Ico (0 : ℝ) 1, gap π V c p E σ ≤ 0 →
      ContinuousOn (fun α => E α σ) (Icc 0 1) → ContinuousOn (π σ) (Ici 0) →
      ∃ α ∈ Icc (0 : ℝ) 1, SolvesFour π V c p E σ α ∧
        IsEquilibrium π V c p E σ (E α σ) α (c / V)) ∧
    (∀ σ ∈ Icc (0 : ℝ) 1, gap π V c p E σ = 0 → SolvesFour π V c p E σ 1) ∧
    SolvesFour π V c p E 1 0 := by sorry

end StrategicObfuscation
