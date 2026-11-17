-- Prove2me | Theorems.Thm_PrivRobustStat_Supplement_theorem_7
-- name    : PrivRobustStat.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:04:22.707321+00:00
-- url     : https://prove2.me/theorems/7d9951c1-fd7c-4af7-a5dc-5e3da43ee40b
-- title:
--   Theorem 7, p.61 — private robust heavy-tailed PCA with $\xi=O(\alpha^{1-2/\ell})$
-- statement:
--   Fix an even integer $\ell\ge4$ and $C_\ell\ge1$. A distribution $D$ on $\mathbb R^d$ is in **Model 2** if it has a finite $\ell$-th moment and $(\mathbb E_D|u^\top(x-\mu)|^\ell)^{1/\ell}\le C_\ell(u^\top\Sigma u)^{1/2}$ for all $u$, where $\mu$ and $\Sigma$ are its mean and covariance; $\|\Sigma\|_{\mathrm{op}}$ is the largest eigenvalue of $\Sigma$. An **$\alpha$-corrupted sample** is $A(X)$, where $X$ is an i.i.d. sample of size $n$ from $D$ and the adversary $A$ replaces at most $\alpha n$ points after seeing $X$.
--
--   There are constants $\alpha_\star,C_\xi,C_n,C_T>0$ depending only on $\ell$ and $C_\ell$ and one algorithm $\mathcal M$ (an admissible program of the Gaussian real RAM reading $d,n,\alpha,\beta,\varepsilon,\delta$ and the data) such that, for all $d\ge1$, $n$, $\alpha\in(0,\alpha_\star)$, $\varepsilon\in(0,1)$, $\delta,\beta\in(0,\tfrac14)$, writing $\xi=C_\xi\,\alpha^{1-2/\ell}$, if $\xi\le\tfrac15$ and
--
--   $$n\ \ge\ C_n\left(\frac{d+\log(1/\beta)}{\alpha^{2-2/\ell}}+\frac{d}{\alpha^{3-4/\ell}\varepsilon}+\frac{1}{\alpha^{7/2-5/\ell}\varepsilon}\right)\log^8\Big(\frac{d}{\alpha\varepsilon\delta\beta}\Big),$$
--
--   then:
--   1. on every input and tape, $\mathcal M$ halts within $C_T\,\frac{nd}{\alpha^{3-6/\ell}}\log^5\frac{nd}{\alpha\beta}$ steps, its output $\hat u$ is a measurable function of the tape, and $\|\hat u\|_2=1$;
--   2. $\mathcal M$ is $(\varepsilon,\delta)$-differentially private on all pairs of neighbouring datasets;
--   3. for every $D$ in Model 2 with $\mu=0$ and every adversary $A$, with probability at least $1-\beta$,
--
--   $$\hat u^\top\Sigma\,\hat u\ \ge\ (1-\xi)\,\|\Sigma\|_{\mathrm{op}} .$$
--
--   This is private and robust PCA for heavy-tailed distributions with only $\ell$ hypercontractive moments, in the quadratic-form notion of suboptimality.
--
--   **Formalization Note** Machine, input layout, privacy and the lower-integral accuracy clause have the shape of the published goal `PrivRobustStat.theorem_4`. Powers with exponents depending on $\ell$ are real powers.
--
--   Differences from the source:
--   - reading: "There is an algorithm" (no machine named) → one finite admissible program of the published Gaussian real RAM PrivRobustStat.Machine (rational literals, + − × ÷, √, powers, log, floor, Gaussian draws, unit cost per instruction), reading d, n, α, β, ε, δ from its input; reason: the paper names no machine; the same reading as the published goal PrivRobustStat.theorem_4
--   - reading: "for appropriate constants depending only on ℓ and Cℓ" → ∀ even ℓ ≥ 4, ∀ C_ℓ ≥ 1, ∃ α⋆, C_ξ, C_n, C_T > 0 and one program, before d, n, α, ε, δ, β; reason: the paper's own quantifier order; the program may use a rational upper bound on C_ℓ since Model 2 is monotone in C_ℓ
--   - reading: "runs in time …" → on every tape and every dataset (any reals) the run halts within the bound; reason: worst-case running time, as in theorem_4
--   - reading: (ε, δ)-DP estimate → IsApproxDP over every pair of neighbouring datasets in (ℝ^d)^n, with the output a measurable function of the tape; reason: privacy is a worst-case notion (p.12); measurability makes the output law the genuine pushforward
--   - reading: "with probability at least 1 − β" on an α-corrupted sample → lower integral over D^⊗n of the tape probability of the success event at A X, for every adversary A changing at most αn points (any map); reason: meaningful for non-measurable adversaries; for a measurable one it is the probability of the joint event; as in theorem_4
--   - reading: "return an (ε, δ)-DP unit vector û" → ∥û∥₂ = 1 on every tape and every dataset, and the success event û⊤Σû ≥ (1 − ξ)·∥Σ∥_op with ∥Σ∥_op = HighDimStat.Pca.opNormSymm Σ = sup_{∥v∥₂=1} |v⊤Σv|; reason: the literal reading of Problems 3–4; the operator norm of the symmetric matrix Σ
--   - encoding: ξ = O(α^{1−2/ℓ}), provided ξ ∈ (0, 1/5]; n = Ω(((d + log(1/β))/α^{2−2/ℓ} + d/(α^{3−4/ℓ}ε) + 1/(α^{7/2−5/ℓ}ε)) log⁸(d/(αεδβ))); time O(nd/α^{3−6/ℓ} log⁵(nd/(αβ))) → ξ := C_ξ·α^{1−2/ℓ} with hypothesis ξ ≤ 1/5; C_n·(…)·log⁸(d/(αεδβ)) ≤ n; work ≤ C_T·(nd/α^{3−6/ℓ})·log⁵(nd/(αβ)); real powers; reason: meaning of O and Ω; ξ > 0 is automatic for α > 0
--   - encoding: Model 2 with µ = 0_d → IsModel2 ℓ C_ℓ D (finite ℓ-th moment and the hypercontractive bound) and popMean D = 0; reason: the moments exist under MemLp id ℓ; Lean integrals of non-integrable functions are 0
--   - encoding: input and output of the algorithm → the published layout PrivRobustStat.goalInput (d, n in integer memory; α, β, ε, δ, x₁, …, x_n in real memory), output read from the first halted state; d ≥ 1; reason: the paper names no format; same as theorem_4
-- source:
--   Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, Efficient Private and Robust Statistics, STOC 2027 submission (manuscript sha256 1a69e17a…), Theorem 7, p.61 (PDF p.64); Problem 3 and Model 2, p.14 (PDF p.17); Definition 1, p.11; DP, p.12

import Mathlib
import Definitions.Def_PrivRobustStat_Machine
import Definitions.Def_PrivRobustStat_Privacy
import Definitions.Def_PrivRobustStat_Model
import Definitions.Def_HighDimStat_Pca_OpNormSymm
import Definitions.Def_PrivRobustStat_Supplement_Models

open MeasureTheory ProbabilityTheory

namespace PrivRobustStat.Supplement

/-- **Theorem 7** (heavy-tailed PCA), p.61 (PDF p.64); Problem 3 and Model 2, p.14;
Definition 1, p.11; DP, p.12.

Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, *Efficient Private and Robust Statistics*, STOC 2027
submission (manuscript sha256 1a69e17a…).

"Let α ∈ (0, α⋆), ε ∈ (0, 1), and (δ, β) ∈ (0, 1/4)². There is an algorithm that solves Problem 3
with accuracy ξ = O(α^{1−2/ℓ}), provided ξ ∈ (0, 1/5] and n = Ω( ( (d + log(1/β))/α^{2−2/ℓ} +
d/(α^{3−4/ℓ}ε) + 1/(α^{7/2−5/ℓ}ε) ) log⁸( d/(αεδβ) ), ) for appropriate constants depending only
on ℓ and Cℓ. The algorithm runs in time O( nd/α^{3−6/ℓ} log⁵( nd/(αβ) ) )."

For every even integer `ℓ ≥ 4` and every `C_ℓ ≥ 1` there are constants `α⋆, C_ξ, C_n, C_T > 0` and
one admissible program `P` of the Gaussian real RAM such that for all `d ≥ 1`, `n`, `α ∈ (0, α⋆)`,
`ε ∈ (0, 1)`, `δ, β ∈ (0, 1/4)`, writing `ξ := C_ξ·α^{1−2/ℓ}`, if `ξ ≤ 1/5` and
`n ≥ C_n·((d + log(1/β))/α^{2−2/ℓ} + d/(α^{3−4/ℓ}ε) + 1/(α^{7/2−5/ℓ}ε))·log⁸(d/(αεδβ))`, then on
input `(d, n, α, β, ε, δ, x[n])`:
1. every Gaussian tape and every dataset halts with `work ≤ C_T·(nd/α^{3−6/ℓ})·log⁵(nd/(αβ))`;
2. the output is a measurable function of the tape;
3. the output `û` is a unit vector on every tape and every dataset;
4. the mechanism is `(ε, δ)`-DP over all pairs of neighbouring datasets in `(ℝ^d)^n`;
5. for every distribution `D` in Model 2 with parameters `(ℓ, C_ℓ)` and mean `µ = 0`, and every
   adversary `A` replacing at most `αn` points, `û⊤Σû ≥ (1 − ξ)∥Σ∥_op` with probability at least
   `1 − β`, where `Σ` is the covariance of `D`.

**Formalization Note.**
* Machine, input layout, output, DP and the accuracy clause have the shape of the published
  `PrivRobustStat.theorem_4`.
* `ℓ` and `C_ℓ` are quantified before the constants and the program ("constants depending only on
  ℓ and Cℓ").
* Exponents involving `ℓ` are real powers (`Real.rpow`) with `ℓ` cast to `ℝ`.
* "provided ξ ∈ (0, 1/5]" is the hypothesis `C_ξ·α^{1−2/ℓ} ≤ 1/5` on the same `C_ξ`; positivity is
  automatic for `α > 0`.
* `∥Σ∥_op` is `HighDimStat.Pca.opNormSymm`, `sup_{∥v∥₂ = 1} |v⊤Σv|`, the ℓ2 operator norm of the
  symmetric matrix `Σ`. -/
theorem theorem_7 :
    ∀ ℓ : ℕ, Even ℓ → 4 ≤ ℓ → ∀ Cℓ : ℝ, 1 ≤ Cℓ →
    ∃ αstar : ℝ, 0 < αstar ∧ ∃ Cξ : ℝ, 0 < Cξ ∧ ∃ Cn : ℝ, 0 < Cn ∧ ∃ CT : ℝ, 0 < CT ∧
      ∃ P : Program, Admissible P ∧
        ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, ∀ α ε δ β : ℝ, 0 < α → α < αstar → 0 < ε → ε < 1 →
          0 < δ → δ < 1 / 4 → 0 < β → β < 1 / 4 →
          Cξ * α ^ (1 - 2 / (ℓ : ℝ)) ≤ 1 / 5 →
          Cn * ((((d : ℝ) + Real.log (1 / β)) / α ^ (2 - 2 / (ℓ : ℝ)) +
              (d : ℝ) / (α ^ (3 - 4 / (ℓ : ℝ)) * ε) +
              1 / (α ^ ((7 : ℝ) / 2 - 5 / (ℓ : ℝ)) * ε)) *
              Real.log ((d : ℝ) / (α * ε * δ * β)) ^ 8) ≤ n →
          (∀ (X : Fin n → Vec d) (ω : ℕ → ℝ), ∃ t : ℕ,
            (run P (goalInput d n α β ε δ X) ω t).halted = true ∧
            ((run P (goalInput d n α β ε δ X) ω t).work : ℝ) ≤
              CT * ((n : ℝ) * d / α ^ (3 - 6 / (ℓ : ℝ))) *
                Real.log ((n : ℝ) * d / (α * β)) ^ 5) ∧
          (∀ X : Fin n → Vec d, Measurable fun ω => output P d (goalInput d n α β ε δ X) ω) ∧
          (∀ (X : Fin n → Vec d) (ω : ℕ → ℝ), ‖output P d (goalInput d n α β ε δ X) ω‖ = 1) ∧
          IsApproxDP (fun X : Fin n → Vec d =>
            gaussTape.map fun ω => output P d (goalInput d n α β ε δ X) ω) ε δ ∧
          ∀ (D : Measure (Vec d)) [IsProbabilityMeasure D], IsModel2 ℓ Cℓ D → popMean D = 0 →
            ∀ A : (Fin n → Vec d) → (Fin n → Vec d), IsAdversary α A →
              ENNReal.ofReal (1 - β) ≤
                ∫⁻ X, gaussTape {ω | (1 - Cξ * α ^ (1 - 2 / (ℓ : ℝ))) *
                    HighDimStat.Pca.opNormSymm (popCov D) ≤
                  quadForm (popCov D) (output P d (goalInput d n α β ε δ (A X)) ω)}
                  ∂(Measure.pi fun _ : Fin n => D) := by sorry

end PrivRobustStat.Supplement
