-- Prove2me | Theorems.Thm_TimeInconsLQ_Deterministic_lambda_identity
-- name    : TimeInconsLQ.Deterministic.lambda_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:34:08.847677+00:00
-- url     : https://prove2.me/theorems/7d42d175-4c25-46d9-868e-47a16f1cc11f
-- title:
--   Proof of Theorem 4.4, p. 14 — Λ(s; t) = N_s[X*_s − E_t X*_s]B_s + Γ⁽¹⁾_s(X*_s − X*_t)B_s, and Λ satisfies (3.4)
-- statement:
--   Consider the scalar-state problem with deterministic coefficients of §4 under the standing assumptions, with $G\ge h>0$ and one of the cases (i)–(iii) of Theorem 4.4. Let $(M,N)$ be a positive solution pair of (4.9), $\Phi$ a solution of (4.8), $X^*$ a closed-loop state of the feedback $u^*_s=\alpha_sX^*_s+\beta_s$ of (4.4), and, for each $t\in[0,T)$, $Y^t$ a progressive version of $s\mapsto\mathbb E_t[X^*_s]$ on $[t,T]$. Define $p,k$ by (4.1), (4.3) and $\Lambda(s;t)=R_su^*_s+p(s;t)B_s+D_s'k(s;t)$.
--
--   **Claim.**
--   1. For $0\le t\le s\le T$ (with $t<T$),
--   $$\Lambda(s;t)=N_s\big[X^*_s-\mathbb E_t[X^*_s]\big]B_s+\Gamma^{(1)}_s(X^*_s-X^*_t)B_s.$$
--   2. $\Lambda$ satisfies condition (3.4): for every $t\in[0,T)$, $\mathbb E_t\int_t^T|\Lambda(s;t)|\,ds<+\infty$ and $\lim_{s\downarrow t}\mathbb E_t[\Lambda(s;t)]=0$ almost surely.
--
--   This verifies the second hypothesis of the sufficient condition (Theorem 3.3) for the explicit candidate.
--
--   **Formalization Note.** In part 1, $\mathbb E_t[X^*_s]$ is the chosen version $Y^t_s$ and the identity holds for every $\omega$ (it is algebra once $R_s+M_sD_s'D_s$ is invertible). Condition (3.4) is stated in the exact and version-robust form described in the `Ansatz` module.
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, p. 14, proof of Theorem 4.4; (3.4) p. 6

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_Deterministic_Model
import Definitions.Def_TimeInconsLQ_Deterministic_Riccati
import Definitions.Def_TimeInconsLQ_Deterministic_Ansatz

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal NNReal

namespace TimeInconsLQ.Deterministic

/-- Proof of Theorem 4.4 (p. 14): with `p, k, u*` from (4.1), (4.3), (4.4) (and `Y t s` a
version of `E_t[X*_s]`), `Λ(s; t) = R_su*_s + p(s; t)B_s + D′_sk(s; t)` equals
`N_s[X*_s − E_t[X*_s]]B_s + Γ⁽¹⁾_s(X*_s − X*_t)B_s` for `0 ≤ t ≤ s ≤ T`, and `Λ` satisfies
condition (3.4). -/
theorem lambda_identity {Ω : Type*} [MeasurableSpace Ω] {l d : ℕ} (c : Coeffs l d)
    (T : ℝ≥0) (hT : 0 < T) (hc : CoeffsStanding c T) (hGh : c.h ≤ c.G) (hh : 0 < c.h)
    (hcase : Case_i c T ∨ Case_ii c T ∨ Case_iii c T)
    (M N Φ : ℝ≥0 → ℝ) (hMN : IsPosSol49 c T M N) (hΦ : IsSol48 c T M N Φ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → Fin d → ℝ) (hW : Peng1990.SMP.IsStdBrownian P W) (x₀ : Fin 1 → ℝ)
    (X : ℝ≥0 → Ω → Fin 1 → ℝ)
    (hX : IsClosedLoop (toData c P W hW T hT x₀)
      (fun s _ => alpha c T M N s) (fun s _ => beta c M Φ s) X)
    (Y : ℝ≥0 → ℝ≥0 → Ω → ℝ)
    (hY : ∀ t : ℝ≥0, t < T → IsCondMeanVersion (toData c P W hW T hT x₀) t X (Y t)) :
    (∀ t : ℝ≥0, t < T → ∀ s : ℝ≥0, t ≤ s → s ≤ T → ∀ ω,
      Lam c (pAnsatz c T M N Φ X (Y t) t) (kAnsatz c M X (fbControl c T M N Φ X))
          (fbControl c T M N Φ X) s ω
        = (N s * (X s ω 0 - Y t s ω) + Gam1 c T s * (X s ω 0 - X t ω 0)) • c.B s) ∧
    Cond34 (toData c P W hW T hT x₀) (fun t =>
      Lam c (pAnsatz c T M N Φ X (Y t) t) (kAnsatz c M X (fbControl c T M N Φ X))
        (fbControl c T M N Φ X)) := by sorry

end TimeInconsLQ.Deterministic
