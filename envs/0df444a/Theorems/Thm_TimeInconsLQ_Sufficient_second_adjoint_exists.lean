-- Prove2me | Theorems.Thm_TimeInconsLQ_Sufficient_second_adjoint_exists
-- name    : TimeInconsLQ.Sufficient.second_adjoint_exists
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-05T14:09:07.131955+00:00
-- url     : https://prove2.me/theorems/7bcb26b0-4c73-4de7-ad5a-c99fd5df7a88
-- title:
--   §3, pp. 4–5 — the second adjoint equation (3.2) has a solution (P(·;t), K(·;t))
-- statement:
--   Existence of the second adjoint process.
--
--   Work under the standing assumptions of §2 (bounded deterministic $A$, essentially bounded progressively measurable $C^j$ and $Q$, $Q$ symmetric, constant symmetric $G$). For every $t\in[0,T)$ the matrix-valued linear backward SDE (3.2) on $[t,T]$,
--
--   $$
--   \begin{cases}
--   dP(s;t)=-\Big\{A_s'P(s;t)+P(s;t)A_s+\sum_{j=1}^d\big[(C^j_s)'P(s;t)C^j_s+(C^j_s)'K^j(s;t)+K^j(s;t)C^j_s\big]+Q_s\Big\}ds+\sum_{j=1}^dK^j(s;t)\,dW^j_s, & s\in[t,T],\\[2pt]
--   P(T;t)=G,
--   \end{cases}
--   $$
--
--   admits a solution $\big(P(\cdot;t),(K^j(\cdot;t))_{j=1}^d\big)\in L^2_{\mathcal F}(t,T;\mathbb S^n)\times\big(L^2_{\mathcal F}(t,T;\mathbb S^n)\big)^d$, i.e. with $P(s;t)$ and $K^j(s;t)$ symmetric for $s\in[t,T]$.
--
--   In the paper (pp. 4–5) the pair $(P(\cdot;t),K(\cdot;t))$ is introduced as "the solution" of (3.2); this is a linear BSDE with bounded coefficients and bounded terminal value, so it is covered by the standard existence theory of BSDEs. The second adjoint process enters the expansion (3.3) of Proposition 3.1 through $H(s;t)=R_s+\sum_j(D^j_s)'P(s;t)D^j_s$, and is needed to apply Proposition 3.1 in the proof of Theorem 3.2.
--
--   **Formalization Note** "Solution" is the module's `SecondAdjoint`: the BSDE is read entrywise through `Peng1990.SMP.matEntries`, the solution and its martingale integrands are progressively measurable (after cutting off before time $t$) and square integrable on $[t,T]\times\Omega$, the integral form of (3.2) holds almost surely at every $r\in[t,T]$, and $P(s;t),K^j(s;t)$ are symmetric for every $s\in[t,T]$ and every $\omega$.
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, §3, pp. 4–5, (3.2) ("define ... (P(·;t), (K^j(·;t))) ∈ L²_F(t,T;S^n)×(L²_F(t,T;S^n))^d as the solutions")

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_Sufficient_Model
import Definitions.Def_TimeInconsLQ_Sufficient_Adjoint

namespace TimeInconsLQ.Sufficient

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

/-- §3, pp. 4–5: for every `t ∈ [0, T)`, the second adjoint equation (3.2) on `[t, T]`,
`dP(s;t) = −{Aₛᵀ P + P Aₛ + Σⱼ [(Cʲₛ)ᵀ P Cʲₛ + (Cʲₛ)ᵀ Kʲ + Kʲ Cʲₛ] + Qₛ} ds + Σⱼ Kʲ(s;t) dWʲₛ`,
`P(T;t) = G`, admits a solution `(P(·;t), K(·;t)) ∈ L²_𝓕(t, T; Sⁿ) × (L²_𝓕(t, T; Sⁿ))ᵈ`
(a linear BSDE with bounded coefficients; the paper defines `(P, K)` as "the solutions"). -/
theorem second_adjoint_exists {Ω : Type*} [MeasurableSpace Ω] {n l d : ℕ} (M : Data Ω n l d)
    (hM : Standing M) (t : ℝ≥0) (ht : t < M.T) :
    ∃ (Pm : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
      (K : Fin d → ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ), SecondAdjoint M t Pm K := by sorry

end TimeInconsLQ.Sufficient
