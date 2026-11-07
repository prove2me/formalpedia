-- Prove2me | Theorems.Thm_PrivRobustStat_theorem_4
-- name    : PrivRobustStat.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:49:35.079945+00:00
-- url     : https://prove2.me/theorems/6b050e98-5ebf-4ddb-92ff-9c3a5b79b4c4
-- title:
--   Theorem 4, p.33 (corrected: $\log^3 d$ read as $\max\{1,\log d\}^3$) — private robust mean estimation: error $O(\sqrt\alpha)$, $\widetilde O(d/(\alpha\varepsilon))$ samples, $\widetilde O(nd)$ time
-- statement:
--   **Theorem 4** (bounded covariance mean estimation). There are constants $\alpha_\star,C_n,C_\xi,C_T>0$ and one algorithm such that the following holds for all $d\ge1$, $\alpha\in(0,\alpha_\star)$, $\varepsilon\in(0,1)$, $\beta,\delta\in(0,\tfrac14)$ and
--
--   $$n\ge C_n\,\frac d{\alpha\varepsilon}\log^5\Big(\frac d{\alpha\varepsilon\delta\beta}\Big).$$
--
--   On input $(d,n,\alpha,\beta,\varepsilon,\delta,x_{[n]})$:
--
--   1. on every dataset and every outcome of its randomness the algorithm halts within $C_T\,nd\,\max\{1,\log d\}^3\log^2\frac{nd}{\alpha\beta}$ steps;
--   2. it is $(\varepsilon,\delta)$-differentially private;
--   3. for every distribution $D$ of Model 1 with mean $\mu$ and every adversary that replaces at most $\alpha n$ of $n$ i.i.d. samples from $D$, its output $\hat\mu$ satisfies, with probability at least $1-\beta$,
--   $$\|\hat\mu-\mu\|_2\le C_\xi\sqrt\alpha .$$
--
--   The error $O(\sqrt\alpha)$ matches the non-private lower bound under bounded covariance, the sample size matches the private lower bound up to logarithms, and the time is linear in the input size up to logarithms.
--
--   **Formalization Note** "Algorithm" is one admissible program of the Gaussian real RAM `PrivRobustStat.Machine` that reads all parameters from its input. The accuracy probability is the lower integral over the clean sample of the probability over the tape, which is meaningful for non-measurable adversaries.
--
--   Differences from the source:
--   - reading: "There is an algorithm" (no machine named) → one finite admissible program of the Gaussian real RAM PrivRobustStat.Machine: rational literals, + − × ÷, √, |a|^b, log, floor into integer pointers, integer pointer arithmetic, standard Gaussian draws, unit cost per instruction; reason: the paper names no machine; its algorithm needs exact Gaussian noise (Algorithms 2, 4, 7) and bins unbounded reals (Algorithm 6)
--   - reading: "for appropriate constants" → ∃ α⋆, C_n, C_ξ, C_T > 0 and one program before d, n, α, ε, β, δ; the program reads d, n, α, β, ε, δ from its input; reason: the constants are universal (Definition 1, Lemmas 15, 17), and Algorithm 8 takes the parameters as public inputs; a program per parameter value would be the weaker reading
--   - correction: time O(nd log³(d) log²(nd/(αβ))) → work ≤ C_T·n·d·max{1, log d}³·log²(nd/(αβ)); reason: counterexample: d = 1 and any n, α, ε, β, δ in range; the printed bound is 0 because log 1 = 0, while every run executes at least the halting instruction, so its work is ≥ 1; for d ≥ 3 nothing changes
--   - reading: "runs in time …" → on every tape and every dataset (any reals), the run halts within the bound; reason: the loop counts of Algorithm 8 are fixed by public inputs or bounded by n, so the paper's bound is worst case
--   - reading: (ε, δ)-DP (Problem 1) → over every pair of neighbouring datasets in (ℝ^d)^n, with the output a measurable function of the tape; reason: privacy is a worst-case notion (p.12), and Lemma 17 holds on every dataset; measurability makes the law the genuine pushforward
--   - reading: "with probability at least 1 − β" on an α-corrupted sample under Model 1 → lower integral over D^⊗n of the tape probability of the event, for every adversary (any map changing at most αn points); reason: meaningful for non-measurable adversaries; for a measurable one it is the probability of the joint event
--   - encoding: ξ = O(√α); n = Ω(d/(αε) log⁵(d/(αεδβ))) → ∥µ̂ − µ∥₂ ≤ C_ξ√α; C_n·(d/(αε))·log⁵(d/(αεδβ)) ≤ n; reason: meaning of O and Ω with constants independent of every other quantity
--   - encoding: Model 1 → probability measure with MemLp id 2, µ its Bochner mean, E⟨u, x − µ⟩² ≤ ∥u∥² for all u; reason: the mean and covariance exist exactly under a finite second moment
--   - encoding: the input and output of the algorithm → the layout PrivRobustStat.goalInput (d, n in integer memory; α, β, ε, δ, x₁, …, x_n in real memory) and µ̂ in cells −1, …, −d of the first halted state; d ≥ 1; reason: the paper names no format; the time bound pays for reading the nd reals
-- source:
--   Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, Efficient Private and Robust Statistics, STOC 2027 submission (manuscript sha256 1a69e17a…), Theorem 4, p.33 (PDF p.36); Problem 1 and Model 1, p.14; Definition 1, p.11; DP, p.12

import Mathlib
import Definitions.Def_PrivRobustStat_Machine
import Definitions.Def_PrivRobustStat_Privacy
import Definitions.Def_PrivRobustStat_Model

open MeasureTheory ProbabilityTheory

namespace PrivRobustStat

/-- **Theorem 4** (bounded covariance mean estimation), p.33 (PDF p.36); Problem 1 and Model 1, p.14;
Definition 1, p.11; DP, p.12.

Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, *Efficient Private and Robust Statistics*, STOC 2027
submission (manuscript sha256 1a69e17a…).

"Let α ∈ (0, α⋆), ε ∈ (0, 1), and (β, δ) ∈ (0, 1/4)². There is an algorithm that solves Problem 1
with ξ = O(√α), provided n = Ω( d/(αε) log⁵( d/(αεδβ) ) ). for appropriate constants. The algorithm
runs in time O( nd log³(d) log²( nd/(αβ) ) )."

There are constants `α⋆, C_n, C_ξ, C_T > 0` and one admissible program `P` of the Gaussian real RAM
such that for all `d ≥ 1`, `n`, `α ∈ (0, α⋆)`, `ε ∈ (0, 1)`, `β, δ ∈ (0, 1/4)` with
`n ≥ C_n·(d/(αε))·log⁵(d/(αεδβ))`, on input `(d, n, α, β, ε, δ, x[n])`:
1. every Gaussian tape and every dataset halts with `work ≤ C_T·n·d·max{1, log d}³·log²(nd/(αβ))`;
2. the output is a measurable function of the tape;
3. the mechanism is `(ε, δ)`-DP over all pairs of neighbouring datasets in `(ℝ^d)^n`;
4. for every Model-1 distribution `D` and every adversary `A` replacing at most `αn` points,
   `∥µ̂ − µ∥₂ ≤ C_ξ√α` with probability at least `1 − β` (lower integral over the clean sample of the
   tape probability).

**Formalization Note.**
* The machine (`Def_PrivRobustStat_Machine`) and the input layout `goalInput` are a reading: the
  paper names none. The program takes `d, n, α, β, ε, δ` as input, as Algorithm 8 does, so one
  program serves all parameters.
* `log³(d)` is read as `max{1, log d}³` (a correction: at `d = 1` the printed bound is `0`, while
  every run executes at least `halt`).
* The lower integral `∫⁻` of a possibly non-measurable integrand makes the accuracy clause meaningful
  for every adversary, measurable or not; for a measurable adversary it is the probability of the
  joint event. -/
theorem theorem_4 :
    ∃ αstar : ℝ, 0 < αstar ∧ ∃ Cn : ℝ, 0 < Cn ∧ ∃ Cξ : ℝ, 0 < Cξ ∧ ∃ CT : ℝ, 0 < CT ∧
      ∃ P : Program, Admissible P ∧
        ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, ∀ α ε β δ : ℝ, 0 < α → α < αstar → 0 < ε → ε < 1 →
          0 < β → β < 1 / 4 → 0 < δ → δ < 1 / 4 →
          Cn * ((d : ℝ) / (α * ε)) * Real.log ((d : ℝ) / (α * ε * δ * β)) ^ 5 ≤ n →
          (∀ (X : Fin n → Vec d) (ω : ℕ → ℝ), ∃ t : ℕ,
            (run P (goalInput d n α β ε δ X) ω t).halted = true ∧
            ((run P (goalInput d n α β ε δ X) ω t).work : ℝ) ≤
              CT * n * d * max 1 (Real.log d) ^ 3 * Real.log ((n : ℝ) * d / (α * β)) ^ 2) ∧
          (∀ X : Fin n → Vec d, Measurable fun ω => output P d (goalInput d n α β ε δ X) ω) ∧
          IsApproxDP (fun X : Fin n → Vec d =>
            gaussTape.map fun ω => output P d (goalInput d n α β ε δ X) ω) ε δ ∧
          ∀ (D : Measure (Vec d)) [IsProbabilityMeasure D], IsModel1 D →
            ∀ A : (Fin n → Vec d) → (Fin n → Vec d), IsAdversary α A →
              ENNReal.ofReal (1 - β) ≤
                ∫⁻ X, gaussTape {ω | ‖output P d (goalInput d n α β ε δ (A X)) ω - popMean D‖ ≤
                  Cξ * Real.sqrt α} ∂(Measure.pi fun _ : Fin n => D) := by sorry

end PrivRobustStat
