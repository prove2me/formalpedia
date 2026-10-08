-- Prove2me | Theorems.Thm_TimeInconsLQ_Deterministic_ansatz_solves_fbsde
-- name    : TimeInconsLQ.Deterministic.ansatz_solves_fbsde
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:26:37.564982+00:00
-- url     : https://prove2.me/theorems/6b469c68-809e-453c-a1c8-70483f2e2f10
-- title:
--   Proof of Theorem 4.4, p. 14 — p(·; ·) and k(·; ·) from (4.1), (4.3) solve the backward equation of (3.10)
-- statement:
--   Consider the scalar-state problem with deterministic coefficients of §4 under the standing assumptions, with $G\ge h>0$ and one of the cases (i)–(iii) of Theorem 4.4. Let $(M,N)$ be a positive solution pair of (4.9), $\Phi$ a solution of (4.8), and $X^*$ a closed-loop state of the feedback $u^*_s=\alpha_sX^*_s+\beta_s$ of (4.4) on a probability space with a standard Brownian motion $W$.
--
--   **Claim.** For every $t\in[0,T)$ the family $s\mapsto\mathbb E_t[X^*_s]$, $s\in[t,T]$, has a progressive version; and for every such version, the processes
--   $$p(s;t)=M_sX^*_s-N_s\mathbb E_t[X^*_s]-\Gamma^{(1)}_sX^*_t+\Phi_s,\qquad k(s;t)=M_s[C_sX^*_s+D_su^*_s+\sigma_s]$$
--   of (4.1) and (4.3) solve, on $[t,T]$, the backward equation of (3.10):
--   $$dp(s;t)=-[A_sp(s;t)+C_s'k(s;t)+Q_sX^*_s]\,ds+k(s;t)'dW_s,\qquad p(T;t)=GX^*_T-h\mathbb E_t[X^*_T]-\mu_1X^*_t-\mu_2.$$
--   Together with the closed-loop equation, $(u^*,X^*,p,k)$ solves the system (3.10).
--
--   This verifies the first hypothesis of the sufficient condition (Theorem 3.3) for the explicit candidate.
--
--   **Formalization Note.** $\mathbb E_t[X^*_s]$ is a family of conditional expectations indexed by $s$; the claim quantifies over every progressive version $Y$ with $Y_s=\mathbb E_t[X^*_s]$ a.s. for each $s\in[t,T]$ (and asserts that one exists), so it does not depend on Lean's choice of versions. The backward equation is solved on $[t,T]$ in the sense of the `Ansatz` module (Peng's sign convention, stochastic integrals of $\mathbf 1_{s\ge t}k$).
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, p. 14, proof of Theorem 4.4; (3.10) p. 8; (4.1), (4.3) p. 8

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_Deterministic_Model
import Definitions.Def_TimeInconsLQ_Deterministic_Riccati
import Definitions.Def_TimeInconsLQ_Deterministic_Ansatz

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal NNReal

namespace TimeInconsLQ.Deterministic

/-- Proof of Theorem 4.4 (p. 14): with `u*` given by (4.4) and `X*` a closed-loop state, for
every `t ∈ [0, T)` the family `s ↦ E_t[X*_s]` has a version, and for every version the pair
`(p(·; t), k)` defined by (4.1) and (4.3) solves the backward equation of (3.10) on `[t, T]`:
`dp(s; t) = −[A_sp(s; t) + C′_sk(s; t) + Q_sX*_s] ds + k(s; t)′dW_s`,
`p(T; t) = GX*_T − hE_t[X*_T] − μ₁X*_t − μ₂`. -/
theorem ansatz_solves_fbsde {Ω : Type*} [MeasurableSpace Ω] {l d : ℕ} (c : Coeffs l d)
    (T : ℝ≥0) (hT : 0 < T) (hc : CoeffsStanding c T) (hGh : c.h ≤ c.G) (hh : 0 < c.h)
    (hcase : Case_i c T ∨ Case_ii c T ∨ Case_iii c T)
    (M N Φ : ℝ≥0 → ℝ) (hMN : IsPosSol49 c T M N) (hΦ : IsSol48 c T M N Φ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → Fin d → ℝ) (hW : Peng1990.SMP.IsStdBrownian P W) (x₀ : Fin 1 → ℝ)
    (X : ℝ≥0 → Ω → Fin 1 → ℝ)
    (hX : IsClosedLoop (toData c P W hW T hT x₀)
      (fun s _ => alpha c T M N s) (fun s _ => beta c M Φ s) X) :
    (∀ t : ℝ≥0, t < T → ∃ Y, IsCondMeanVersion (toData c P W hW T hT x₀) t X Y) ∧
    ∀ t : ℝ≥0, t < T → ∀ Y, IsCondMeanVersion (toData c P W hW T hT x₀) t X Y →
      SolvesBSDEOn (TimeInconsLQ.Sufficient.filt (toData c P W hW T hT x₀)) P t T W
        (terminal310 c (toData c P W hW T hT x₀) X t) (driver310 c X)
        (pAnsatz c T M N Φ X Y t) (kAnsatz c M X (fbControl c T M N Φ X)) := by sorry

end TimeInconsLQ.Deterministic
