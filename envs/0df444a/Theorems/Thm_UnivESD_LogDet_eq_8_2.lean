-- Prove2me | Theorems.Thm_UnivESD_LogDet_eq_8_2
-- name    : UnivESD.LogDet.eq_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:58.591922+00:00
-- url     : https://prove2.me/theorems/d26a62d1-a0e1-4fe8-944c-7d605843e7d5
-- title:
--   (8.2), p. 2055 — $\frac1n\sum_i(\log\sqrt{\sigma_i^2+\varepsilon_n}-\log\sigma_i)\to0$ almost surely
-- statement:
--   Let $A_n=M_n+X_n$ be as in Theorem 1.5, fix $z\in\mathbb C$, and let $\varepsilon_n>0$ be any deterministic sequence with $\varepsilon_n\to0$. Write $\sigma_i=\sigma_i\big(\tfrac1{\sqrt n}A_n-zI\big)$. Then, almost surely, all $\sigma_1,\dots,\sigma_n$ are positive for all but finitely many $n$, and
--   $$\frac1n\sum_{i=1}^n\Big(\log\sqrt{\sigma_i^2+\varepsilon_n}-\log\sigma_i\Big)\longrightarrow0 .$$
--
--   Since $\frac1n\sum_i\log\sigma_i=\frac1n\log|\det(\frac1{\sqrt n}A_n-zI)|$ and $\frac1n\sum_i\log\sqrt{\sigma_i^2+\varepsilon_n}=\frac1{2n}\log\det\big((\tfrac1{\sqrt n}A_n-zI)(\tfrac1{\sqrt n}A_n-zI)^*+\varepsilon_nI\big)$, this is the step that makes statements (ii) and (iii) of Theorem 1.15 equivalent.
--
--   **Formalization Note** The statement quantifies over every positive sequence $\varepsilon_n\to0$; the paper proves it for the $\varepsilon_n$ of (iii), using only these two properties. The eventual positivity of the $\sigma_i$ is part of the conclusion because Lean's $\log0=0$ would otherwise replace the paper's $+\infty$ term $-\log\sigma_i$ by a finite one. Singular values are one-based. The array coupling of the model is used, since the statement is almost sure in $n$.
-- source:
--   Tao, Vu, Random matrices: Universality of ESDs and the circular law, Ann. Probab. 38 (2010), no. 5, pp. 2055–2056 (PDF 33–34), §8, proof of Theorem 1.15, (8.2)

import Mathlib
import Definitions.Def_UnivESD_LogDet_Basic
import Definitions.Def_UnivESD_LogDet_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace UnivESD.LogDet

/-- (8.2) converges almost surely to zero, Tao–Vu, Ann. Probab. 38 (2010), §8, pp. 2055–2056.
For `A_n` as in Theorem 1.5, every `z ∈ ℂ` and every sequence `ε_n > 0` with `ε_n → 0`, almost
surely: eventually all singular values `σ_i = σ_i(A_n/√n − zI)`, `1 ≤ i ≤ n`, are positive, and
`(1/n) Σ_{i=1}^n (log √(σ_i² + ε_n) − log σ_i) → 0`. -/
theorem eq_8_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (xs : ℕ → ℕ → Ω → ℂ) (hxs : IIDArray P xs)
    (M : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) (hM : HSBound M) (z : ℂ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) :
    ∀ᵐ ω ∂P,
      (∀ᶠ n in atTop, ∀ i ∈ Finset.Icc 1 n, 0 < sv (shiftA M xs z n ω) i) ∧
      Tendsto (fun n : ℕ => (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc 1 n,
          (Real.log (Real.sqrt (sv (shiftA M xs z n ω) i ^ 2 + ε n))
            - Real.log (sv (shiftA M xs z n ω) i)))
        atTop (𝓝 0) := by sorry

end UnivESD.LogDet
