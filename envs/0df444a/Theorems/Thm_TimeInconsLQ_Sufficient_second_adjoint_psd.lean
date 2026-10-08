-- Prove2me | Theorems.Thm_TimeInconsLQ_Sufficient_second_adjoint_psd
-- name    : TimeInconsLQ.Sufficient.second_adjoint_psd
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:32.292505+00:00
-- url     : https://prove2.me/theorems/b3591b73-b925-4e03-9c1f-bf5c9cee95f1
-- title:
--   §3, p. 5 — the second adjoint process is positive semidefinite: P(s;t) ⪰ 0
-- statement:
--   Assume the standing assumptions of the time-inconsistent LQ model (in particular $Q_s\succeq0$ a.e. and $G\succeq0$). Let $t\in[0,T)$ and let $(P(\cdot;t),K(\cdot;t))$, with values in the symmetric $n\times n$ matrices, solve the second adjoint equation
--
--   $$dP(s;t)=-\Big\{A_s'P+PA_s+\sum_{j=1}^d\big[(C^j_s)'PC^j_s+(C^j_s)'K^j+K^jC^j_s\big]+Q_s\Big\}ds+\sum_{j=1}^dK^j(s;t)\,dW^j_s,\quad s\in[t,T],\qquad P(T;t)=G.\qquad(3.2)$$
--
--   Then for every $s\in[t,T]$,
--
--   $$P(s;t)\succeq0\quad\text{almost surely.}$$
--
--   This is the fact the paper uses to deduce $H(s;t)\succeq0$, which lets the quadratic term of the expansion (3.3) be dropped in the proof of Theorem 3.2.
--
--   **Formalization Note.** "$P(s;t)\succeq0$" is asserted for every $s\in[t,T]$, almost surely; the BSDE identity holds for every $s$ almost surely, so this is version-robust. Positive semidefiniteness is Mathlib's `Matrix.PosSemidef` (symmetric with nonnegative quadratic form).
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, p. 5, §3, sentence after (3.2)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_Sufficient_Model
import Definitions.Def_TimeInconsLQ_Sufficient_Adjoint

namespace TimeInconsLQ.Sufficient

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

/-- §3, p. 5: under the standing assumptions (`Q ⪰ 0`, `G ⪰ 0`), every solution `(P(·;t), K(·;t))`
of the second adjoint equation (3.2) on `[t, T]` has `P(s;t) ⪰ 0` almost surely, for every
`s ∈ [t, T]`. -/
theorem second_adjoint_psd {Ω : Type*} [MeasurableSpace Ω] {n l d : ℕ} (M : Data Ω n l d)
    (hM : Standing M) (t : ℝ≥0) (ht : t < M.T)
    (Pm : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
    (K : Fin d → ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
    (hP : SecondAdjoint M t Pm K) :
    ∀ s : ℝ≥0, t ≤ s → s ≤ M.T → ∀ᵐ ω ∂M.P, (Pm s ω).PosSemidef := by sorry

end TimeInconsLQ.Sufficient
