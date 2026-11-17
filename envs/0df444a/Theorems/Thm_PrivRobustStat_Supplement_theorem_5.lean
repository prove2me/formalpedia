-- Prove2me | Theorems.Thm_PrivRobustStat_Supplement_theorem_5
-- name    : PrivRobustStat.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:03:10.588856+00:00
-- url     : https://prove2.me/theorems/eb023b5c-b38b-4dd9-8ec2-ad140ab92483
-- title:
--   Theorem 5, p.39 (corrected: $\log^3 d$ read as $\max\{1,\log d\}^3$) — private robust sub-Gaussian mean estimation with error $O(\alpha\sqrt{\log(1/\alpha)})$
-- statement:
--   Fix $\theta\ge1$. A distribution $D$ on $\mathbb R^d$ is in **Model 3** if $\mathbb E_D[\exp(u^\top(x-\mu))]\le\exp(\theta u^\top\Sigma u/2)$ for all $u$, where $\mu$ and $\Sigma$ are its mean and covariance. An **$\alpha$-corrupted sample** is $A(X)$, where $X=(x_1,\dots,x_n)$ is i.i.d. from $D$ and the adversary $A$ inspects $X$ and replaces at most $\alpha n$ points arbitrarily.
--
--   There are constants $\alpha_\star,C_n,C_\xi,C_T>0$ (depending on $\theta$) and one algorithm $\mathcal M$ (an admissible program of the Gaussian real RAM, which reads $d,n,\alpha,\beta,\varepsilon,\delta$ and the data) such that for all $d\ge1$, $n$, $\alpha\in(0,\alpha_\star)$, $\varepsilon\in(0,1)$ and $\beta,\delta\in(0,\tfrac14)$ with
--
--   $$n\ \ge\ C_n\left(\frac{d+\log\frac1{\alpha\beta}}{\alpha^2}+\frac{d}{\alpha\varepsilon}\log^5\Big(\frac{d}{\alpha\varepsilon\delta\beta}\Big)\right):$$
--
--   1. on every input and every random tape, $\mathcal M$ halts after at most $C_T\,nd\,\max\{1,\log d\}^3\log^2\frac{nd}{\alpha\beta}$ steps, and its output is a measurable function of the tape;
--   2. $\mathcal M$ is $(\varepsilon,\delta)$-differentially private on all pairs of neighbouring datasets;
--   3. for every $D$ in Model 3 with $\Sigma=I$ and every adversary $A$, with probability at least $1-\beta$,
--
--   $$\|\hat\mu-\mu\|_2\ \le\ C_\xi\,\alpha\sqrt{\log(1/\alpha)} .$$
--
--   Under sub-Gaussian tails with identity covariance this improves the $O(\sqrt\alpha)$ error of the bounded-covariance estimator (Theorem 4) to the information-theoretically natural $O(\alpha\sqrt{\log(1/\alpha)})$, at the same nearly linear running time.
--
--   **Formalization Note** Machine, input layout, privacy and accuracy clauses are those of the published goal `PrivRobustStat.theorem_4`. The accuracy clause is a lower integral over the clean sample of the tape probability, so it applies to every adversary, measurable or not.
--
--   Differences from the source:
--   - reading: "There is an algorithm" (no machine named) → one finite admissible program of the published Gaussian real RAM PrivRobustStat.Machine (rational literals, + − × ÷, √, powers, log, floor, Gaussian draws, unit cost per instruction), reading d, n, α, β, ε, δ from its input; reason: the paper names no machine; the same reading as the published goal PrivRobustStat.theorem_4
--   - reading: "for appropriate constants" (Model 3: "for a constant θ ≥ 1") → ∀ θ ≥ 1, ∃ α⋆, C_n, C_ξ, C_T > 0 and one program, before d, n, α, ε, β, δ; reason: θ is a constant of the model; an error uniform in θ is not claimed (the paper fixes θ as a constant, Theorem 6 says so explicitly); the program may use a rational upper bound on θ since Model 3 is monotone in θ
--   - correction: time O(nd log³(d) log²(nd/(αβ))) → work ≤ C_T·n·d·max{1, log d}³·log²(nd/(αβ)); reason: counterexample: d = 1 and any n, α, ε, β, δ in range make the printed bound 0, while every halting run executes at least the halt instruction, work ≥ 1; the same correction as the published theorem_4; nothing changes for d ≥ 3
--   - reading: "runs in time …" → on every tape and every dataset (any reals) the run halts within the bound; reason: worst-case running time, as in theorem_4
--   - reading: (ε, δ)-DP estimate → IsApproxDP over every pair of neighbouring datasets in (ℝ^d)^n, with the output a measurable function of the tape; reason: privacy is a worst-case notion (p.12); measurability makes the output law the genuine pushforward
--   - reading: "with probability at least 1 − β" on an α-corrupted sample → lower integral over D^⊗n of the tape probability of the success event at A X, for every adversary A changing at most αn points (any map); reason: meaningful for non-measurable adversaries; for a measurable one it is the probability of the joint event; as in theorem_4
--   - encoding: ξ = O(α√log(1/α)); n = Ω((d + log(1/(αβ)))/α² + d/(αε) log⁵(d/(αεδβ))) → ∥µ̂ − µ∥₂ ≤ C_ξ·α·√log(1/α); C_n·((d + log(1/(αβ)))/α² + (d/(αε))·log⁵(d/(αεδβ))) ≤ n; reason: meaning of O and Ω with constants independent of d, n, α, ε, β, δ, D
--   - encoding: Model 3 with Σ = I → IsModel3 θ D (finite second moment, integrable exponential moments, MGF bound) and popCov D = 1; reason: mean and covariance exist under a finite second moment; Lean integrals of non-integrable functions are 0
--   - encoding: input and output of the algorithm → the published layout PrivRobustStat.goalInput (d, n in integer memory; α, β, ε, δ, x₁, …, x_n in real memory), output read from the first halted state; d ≥ 1; reason: the paper names no format; same as theorem_4
-- source:
--   Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, Efficient Private and Robust Statistics, STOC 2027 submission (manuscript sha256 1a69e17a…), Theorem 5, p.39 (PDF p.42); Problem 2 and Model 3, p.14 (PDF p.17); Definition 1, p.11; DP, p.12

import Mathlib
import Definitions.Def_PrivRobustStat_Machine
import Definitions.Def_PrivRobustStat_Privacy
import Definitions.Def_PrivRobustStat_Model
import Definitions.Def_PrivRobustStat_Supplement_Models

open MeasureTheory ProbabilityTheory

namespace PrivRobustStat.Supplement

/-- **Theorem 5** (sub-Gaussian mean estimation), p.39 (PDF p.42); Problem 2 and Model 3, p.14;
Definition 1, p.11; DP, p.12.

Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, *Efficient Private and Robust Statistics*, STOC 2027
submission (manuscript sha256 1a69e17a…).

"Let α ∈ (0, α⋆), ε ∈ (0, 1), and (β, δ) ∈ (0, 1/4)². There is an algorithm that solves Problem 2
with ξ = O(α√log(1/α)), provided n = Ω( (d + log(1/(αβ)))/α² + d/(αε) log⁵( d/(αεδβ) ) ). for
appropriate constants. The algorithm runs in time O( nd log³(d) log²( nd/(αβ) ) )."

For every `θ ≥ 1` there are constants `α⋆, C_n, C_ξ, C_T > 0` and one admissible program `P` of the
Gaussian real RAM such that for all `d ≥ 1`, `n`, `α ∈ (0, α⋆)`, `ε ∈ (0, 1)`, `β, δ ∈ (0, 1/4)`
with `n ≥ C_n·((d + log(1/(αβ)))/α² + (d/(αε))·log⁵(d/(αεδβ)))`, on input `(d, n, α, β, ε, δ, x[n])`:
1. every Gaussian tape and every dataset halts with `work ≤ C_T·n·d·max{1, log d}³·log²(nd/(αβ))`;
2. the output is a measurable function of the tape;
3. the mechanism is `(ε, δ)`-DP over all pairs of neighbouring datasets in `(ℝ^d)^n`;
4. for every distribution `D` in Model 3 with parameter `θ` and covariance `Σ = I`, and every
   adversary `A` replacing at most `αn` points, `∥µ̂ − µ∥₂ ≤ C_ξ·α·√log(1/α)` with probability at
   least `1 − β`.

**Formalization Note.**
* Machine, input layout, output, DP and the accuracy clause are exactly those of the published
  `PrivRobustStat.theorem_4`.
* `θ` is quantified before the constants and the program: Model 3 calls `θ` "a constant".
* `log³(d)` is read as `max{1, log d}³` (a correction: at `d = 1` the printed bound is `0`, while
  every run executes at least `halt`).
* `Σ = I` is `popCov D = 1`, an equality of matrices. -/
theorem theorem_5 :
    ∀ θ : ℝ, 1 ≤ θ →
    ∃ αstar : ℝ, 0 < αstar ∧ ∃ Cn : ℝ, 0 < Cn ∧ ∃ Cξ : ℝ, 0 < Cξ ∧ ∃ CT : ℝ, 0 < CT ∧
      ∃ P : Program, Admissible P ∧
        ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, ∀ α ε β δ : ℝ, 0 < α → α < αstar → 0 < ε → ε < 1 →
          0 < β → β < 1 / 4 → 0 < δ → δ < 1 / 4 →
          Cn * (((d : ℝ) + Real.log (1 / (α * β))) / α ^ 2 +
              ((d : ℝ) / (α * ε)) * Real.log ((d : ℝ) / (α * ε * δ * β)) ^ 5) ≤ n →
          (∀ (X : Fin n → Vec d) (ω : ℕ → ℝ), ∃ t : ℕ,
            (run P (goalInput d n α β ε δ X) ω t).halted = true ∧
            ((run P (goalInput d n α β ε δ X) ω t).work : ℝ) ≤
              CT * n * d * max 1 (Real.log d) ^ 3 * Real.log ((n : ℝ) * d / (α * β)) ^ 2) ∧
          (∀ X : Fin n → Vec d, Measurable fun ω => output P d (goalInput d n α β ε δ X) ω) ∧
          IsApproxDP (fun X : Fin n → Vec d =>
            gaussTape.map fun ω => output P d (goalInput d n α β ε δ X) ω) ε δ ∧
          ∀ (D : Measure (Vec d)) [IsProbabilityMeasure D], IsModel3 θ D → popCov D = 1 →
            ∀ A : (Fin n → Vec d) → (Fin n → Vec d), IsAdversary α A →
              ENNReal.ofReal (1 - β) ≤
                ∫⁻ X, gaussTape {ω | ‖output P d (goalInput d n α β ε δ (A X)) ω - popMean D‖ ≤
                  Cξ * α * Real.sqrt (Real.log (1 / α))} ∂(Measure.pi fun _ : Fin n => D) := by sorry

end PrivRobustStat.Supplement
