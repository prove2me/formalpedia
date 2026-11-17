-- Prove2me | Theorems.Thm_PrivRobustStat_Supplement_theorem_6
-- name    : PrivRobustStat.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:03:42.728655+00:00
-- url     : https://prove2.me/theorems/7071bd06-5e70-4afb-afb0-2c76baa3ef8a
-- title:
--   Theorem 6, p.57 — private robust sub-Gaussian PCA with $\xi=O(\alpha\log(1/\alpha))$
-- statement:
--   Fix $\theta\ge1$. A distribution $D$ on $\mathbb R^d$ is in **Model 3** if $\mathbb E_D[\exp(u^\top(x-\mu))]\le\exp(\theta u^\top\Sigma u/2)$ for all $u$, where $\mu$ and $\Sigma$ are its mean and covariance; $\|\Sigma\|_{\mathrm{op}}$ is the largest eigenvalue of $\Sigma$. An **$\alpha$-corrupted sample** is $A(X)$, where $X$ is an i.i.d. sample of size $n$ from $D$ and the adversary $A$ replaces at most $\alpha n$ points after seeing $X$.
--
--   There are constants $\alpha_\star,C_\xi,C_n,C_T>0$ depending only on $\theta$ and one algorithm $\mathcal M$ (an admissible program of the Gaussian real RAM reading $d,n,\alpha,\beta,\varepsilon,\delta$ and the data) such that, for all $d\ge1$, $n$, $\alpha\in(0,\alpha_\star)$, $\varepsilon\in(0,1)$, $\beta,\delta\in(0,\tfrac14)$, writing $\xi=C_\xi\,\alpha\log(1/\alpha)$, if $\xi\le\tfrac15$ and
--
--   $$n\ \ge\ C_n\left(\frac{d+\log\frac1\beta}{\alpha^2}+\frac{d}{\alpha^2\varepsilon}+\frac{d}{\alpha^{7/3}\varepsilon^{2/3}}\right)\log^8\Big(\frac{d}{\alpha\varepsilon\delta\beta}\Big),$$
--
--   then:
--   1. on every input and tape, $\mathcal M$ halts within $C_T\,\frac{nd}{\alpha^3}\log^5\frac{nd}{\alpha\beta}$ steps, its output $\hat u$ is a measurable function of the tape, and $\|\hat u\|_2=1$;
--   2. $\mathcal M$ is $(\varepsilon,\delta)$-differentially private on all pairs of neighbouring datasets;
--   3. for every $D$ in Model 3 with $\mu=0$ and every adversary $A$, with probability at least $1-\beta$,
--
--   $$\hat u^\top\Sigma\,\hat u\ \ge\ (1-\xi)\,\|\Sigma\|_{\mathrm{op}} .$$
--
--   This is a private and robust principal component analysis under sub-Gaussian tails, in the quadratic-form (energy) notion of suboptimality.
--
--   **Formalization Note** Machine, input layout, privacy and the lower-integral accuracy clause have the shape of the published goal `PrivRobustStat.theorem_4`.
--
--   Differences from the source:
--   - reading: "There is an algorithm" (no machine named) → one finite admissible program of the published Gaussian real RAM PrivRobustStat.Machine (rational literals, + − × ÷, √, powers, log, floor, Gaussian draws, unit cost per instruction), reading d, n, α, β, ε, δ from its input; reason: the paper names no machine; the same reading as the published goal PrivRobustStat.theorem_4
--   - reading: "for appropriate constants depending only on θ" → ∀ θ ≥ 1, ∃ α⋆, C_ξ, C_n, C_T > 0 and one program, before d, n, α, ε, β, δ; reason: the paper's own quantifier order; the program may use a rational upper bound on θ since Model 3 is monotone in θ
--   - reading: "runs in time …" → on every tape and every dataset (any reals) the run halts within the bound; reason: worst-case running time, as in theorem_4
--   - reading: (ε, δ)-DP estimate → IsApproxDP over every pair of neighbouring datasets in (ℝ^d)^n, with the output a measurable function of the tape; reason: privacy is a worst-case notion (p.12); measurability makes the output law the genuine pushforward
--   - reading: "with probability at least 1 − β" on an α-corrupted sample → lower integral over D^⊗n of the tape probability of the success event at A X, for every adversary A changing at most αn points (any map); reason: meaningful for non-measurable adversaries; for a measurable one it is the probability of the joint event; as in theorem_4
--   - reading: "return an (ε, δ)-DP unit vector û" → ∥û∥₂ = 1 on every tape and every dataset, and the success event û⊤Σû ≥ (1 − ξ)·∥Σ∥_op with ∥Σ∥_op = HighDimStat.Pca.opNormSymm Σ = sup_{∥v∥₂=1} |v⊤Σv|; reason: the literal reading of Problems 3–4; the operator norm of the symmetric matrix Σ
--   - encoding: ξ = O(α log(1/α)), provided ξ ∈ (0, 1/5]; n = Ω(((d + log(1/β))/α² + d/(α²ε) + d/(α^{7/3}ε^{2/3})) log⁸(d/(αεδβ))); time O(nd/α³ log⁵(nd/(αβ))) → ξ := C_ξ·α·log(1/α) with hypothesis ξ ≤ 1/5; C_n·(…)·log⁸(d/(αεδβ)) ≤ n; work ≤ C_T·(nd/α³)·log⁵(nd/(αβ)); reason: meaning of O and Ω; the positivity half of ξ ∈ (0, 1/5] is automatic once α⋆ ≤ 1, which the existential α⋆ may ensure, so omitting it changes no instance of the claim
--   - encoding: Model 3 with µ = 0_d → IsModel3 θ D and popMean D = 0; reason: mean and covariance exist under a finite second moment; Lean integrals of non-integrable functions are 0
--   - encoding: input and output of the algorithm → the published layout PrivRobustStat.goalInput (d, n in integer memory; α, β, ε, δ, x₁, …, x_n in real memory), output read from the first halted state; d ≥ 1; reason: the paper names no format; same as theorem_4
-- source:
--   Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, Efficient Private and Robust Statistics, STOC 2027 submission (manuscript sha256 1a69e17a…), Theorem 6, p.57 (PDF p.60); Problem 4 and Model 3, pp.14–15 (PDF pp.17–18); Definition 1, p.11; DP, p.12

import Mathlib
import Definitions.Def_PrivRobustStat_Machine
import Definitions.Def_PrivRobustStat_Privacy
import Definitions.Def_PrivRobustStat_Model
import Definitions.Def_HighDimStat_Pca_OpNormSymm
import Definitions.Def_PrivRobustStat_Supplement_Models

open MeasureTheory ProbabilityTheory

namespace PrivRobustStat.Supplement

/-- **Theorem 6** (sub-Gaussian PCA), p.57 (PDF p.60); Problem 4 and Model 3, pp.14–15;
Definition 1, p.11; DP, p.12.

Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, *Efficient Private and Robust Statistics*, STOC 2027
submission (manuscript sha256 1a69e17a…).

"Let α ∈ (0, α⋆), ε ∈ (0, 1), and (β, δ) ∈ (0, 1/4)². There is an algorithm that solves Problem 4
with ξ = O(α log(1/α)), provided ξ ∈ (0, 1/5] and n = Ω( ( (d + log(1/β))/α² + d/(α²ε) +
d/(α^{7/3} ε^{2/3}) ) log⁸( d/(αεδβ) ) ), for appropriate constants depending only on θ. The
algorithm runs in time O( nd/α³ log⁵( nd/(αβ) ) )."

For every `θ ≥ 1` there are constants `α⋆, C_ξ, C_n, C_T > 0` and one admissible program `P` of the
Gaussian real RAM such that for all `d ≥ 1`, `n`, `α ∈ (0, α⋆)`, `ε ∈ (0, 1)`, `β, δ ∈ (0, 1/4)`,
writing `ξ := C_ξ·α·log(1/α)`, if `ξ ≤ 1/5` and
`n ≥ C_n·((d + log(1/β))/α² + d/(α²ε) + d/(α^{7/3}ε^{2/3}))·log⁸(d/(αεδβ))`, then on input
`(d, n, α, β, ε, δ, x[n])`:
1. every Gaussian tape and every dataset halts with `work ≤ C_T·(nd/α³)·log⁵(nd/(αβ))`;
2. the output is a measurable function of the tape;
3. the output `û` is a unit vector on every tape and every dataset;
4. the mechanism is `(ε, δ)`-DP over all pairs of neighbouring datasets in `(ℝ^d)^n`;
5. for every distribution `D` in Model 3 with parameter `θ` and mean `µ = 0`, and every adversary `A`
   replacing at most `αn` points, `û⊤Σû ≥ (1 − ξ)∥Σ∥_op` with probability at least `1 − β`, where
   `Σ` is the covariance of `D`.

**Formalization Note.**
* Machine, input layout, output, DP and the accuracy clause have the shape of the published
  `PrivRobustStat.theorem_4`.
* `θ` is quantified before the constants and the program ("constants depending only on θ").
* "provided ξ ∈ (0, 1/5]" is the hypothesis `C_ξ·α·log(1/α) ≤ 1/5` on the same `C_ξ`; positivity
  is automatic once `α⋆ ≤ 1`, which the existential `α⋆` may ensure.
* `∥Σ∥_op` is `HighDimStat.Pca.opNormSymm`, `sup_{∥v∥₂ = 1} |v⊤Σv|`, the ℓ2 operator norm of the
  symmetric matrix `Σ`. -/
theorem theorem_6 :
    ∀ θ : ℝ, 1 ≤ θ →
    ∃ αstar : ℝ, 0 < αstar ∧ ∃ Cξ : ℝ, 0 < Cξ ∧ ∃ Cn : ℝ, 0 < Cn ∧ ∃ CT : ℝ, 0 < CT ∧
      ∃ P : Program, Admissible P ∧
        ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, ∀ α ε β δ : ℝ, 0 < α → α < αstar → 0 < ε → ε < 1 →
          0 < β → β < 1 / 4 → 0 < δ → δ < 1 / 4 →
          Cξ * α * Real.log (1 / α) ≤ 1 / 5 →
          Cn * ((((d : ℝ) + Real.log (1 / β)) / α ^ 2 + (d : ℝ) / (α ^ 2 * ε) +
              (d : ℝ) / (α ^ ((7 : ℝ) / 3) * ε ^ ((2 : ℝ) / 3))) *
              Real.log ((d : ℝ) / (α * ε * δ * β)) ^ 8) ≤ n →
          (∀ (X : Fin n → Vec d) (ω : ℕ → ℝ), ∃ t : ℕ,
            (run P (goalInput d n α β ε δ X) ω t).halted = true ∧
            ((run P (goalInput d n α β ε δ X) ω t).work : ℝ) ≤
              CT * ((n : ℝ) * d / α ^ 3) * Real.log ((n : ℝ) * d / (α * β)) ^ 5) ∧
          (∀ X : Fin n → Vec d, Measurable fun ω => output P d (goalInput d n α β ε δ X) ω) ∧
          (∀ (X : Fin n → Vec d) (ω : ℕ → ℝ), ‖output P d (goalInput d n α β ε δ X) ω‖ = 1) ∧
          IsApproxDP (fun X : Fin n → Vec d =>
            gaussTape.map fun ω => output P d (goalInput d n α β ε δ X) ω) ε δ ∧
          ∀ (D : Measure (Vec d)) [IsProbabilityMeasure D], IsModel3 θ D → popMean D = 0 →
            ∀ A : (Fin n → Vec d) → (Fin n → Vec d), IsAdversary α A →
              ENNReal.ofReal (1 - β) ≤
                ∫⁻ X, gaussTape {ω | (1 - Cξ * α * Real.log (1 / α)) *
                    HighDimStat.Pca.opNormSymm (popCov D) ≤
                  quadForm (popCov D) (output P d (goalInput d n α β ε δ (A X)) ω)}
                  ∂(Measure.pi fun _ : Fin n => D) := by sorry

end PrivRobustStat.Supplement
