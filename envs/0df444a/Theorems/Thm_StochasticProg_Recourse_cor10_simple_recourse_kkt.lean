-- Prove2me | Theorems.Thm_StochasticProg_Recourse_cor10_simple_recourse_kkt
-- name    : StochasticProg.Recourse.cor10_simple_recourse_kkt
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-18T04:49:28.725542+00:00
-- url     : https://prove2.me/theorems/515c3c52-7e31-4540-b18e-5bcd87953bc3
-- title:
--   Chapter 3, Corollary 10 -- simple-recourse specialization of Theorem 9
-- statement:
--   **Chapter 3, Corollary 10.** Suppose a simple-recourse problem has a finite optimal value. Then
--   $x^* \in K_1$ is optimal if and only if there exist $\lambda^* \in \mathbb{R}^{m_1}$, $\mu^*
--   \in \mathbb{R}^{n_1}_{\ge 0}$ with $(\mu^*)^{\mathsf T}x^*=0$, and $\pi^* \in
--   \mathbb{R}^{m_2}$ with
--   $$-(q_i^+ - q_i F_i^-(T_{i\cdot}x^*)) \le \pi_i^* \le -(q_i^+ - q_i F_i^+(T_{i\cdot}x^*))
--   \quad (i=1,\dots,m_2),$$
--   such that
--   $$-c + A^{\mathsf T}\lambda^* + \mu^* - (\pi^*)^{\mathsf T}T = 0,$$
--   where $F_i^-, F_i^+$ are the left- and right-hand limits of the distribution function of $h_i$.
--
--   This is Theorem 9 specialised to simple recourse ($W=[I,-I]$) using the explicit closed form of
--   $\partial Q_i(x)$ given by Eq. (1.10).
--
--   **Formalization Note.** The book states (1.10) directly ("has the following simple form") rather
--   than deriving it here from the second-stage LP, so the corollary's hypothesis `hsubdiff` records
--   that closed form for the abstract $Q$ as a hypothesis, exactly as the book's own derivation relies
--   on it as a given fact rather than re-proving it from primitives.
--
--   **Moderator's note.** The book's standing assumption for §3.1c–e (p. 112: "assuming it is not −∞") is stated explicitly: no second-stage problem is unbounded below (`Q(x, ξ_k) ≠ −∞` for every `x` and scenario `k`; for the abstract `Q` of Corollary 10, `Q x ≠ −∞`). Without it "finite on K₂" and the KKT characterisation can fail.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 116, Chapter 3, Corollary 10

import Mathlib
import Definitions.Def_StochasticProg_Recourse_SimpleRecourse

namespace StochasticProg.Recourse

variable {n1 m1 m2 : ℕ}

/-- Chapter 3, Corollary 10 (p. 116): the specialization of Theorem 9 to simple
recourse, using the explicit subdifferential form `∂Q_i(x) = {πT_i· | -q⁺_i +
q_iF⁻_i(T_i·x) ≤ π ≤ -q⁺_i + q_iF⁺_i(T_i·x)}` of Eq. (1.10), where `F⁻_i, F⁺_i` are
the left- and right-hand limits of the distribution function of `h_i` (p. 114); the
book states (1.10) directly rather than deriving it from the second-stage LP, so
`hsubdiff` records that same closed form here as a hypothesis rather than as a
derived fact. `Q` (the aggregate simple-recourse value, Eq. (1.9)) is left abstract,
constrained only by `hsubdiff` and by the subgradient inequality it packages,
exactly as the book leaves it in this corollary. -/
theorem cor10_simple_recourse_kkt (inst : SimpleRecourseInstance n1 m1 m2)
    (Fminus Fplus : Fin m2 → ℝ → ℝ) (Q : (Fin n1 → ℝ) → EReal) (hQ : ∀ x, Q x ≠ ⊥)
    (hsubdiff : ∀ x : Fin n1 → ℝ,
      {η : Fin n1 → ℝ | ∀ y : Fin n1 → ℝ,
          Q x + ((dotProduct η (y - x) : ℝ) : EReal) ≤ Q y} =
        {η | ∃ pi : Fin m2 → ℝ,
          (∀ i, -(inst.qplus i) + inst.qsum i * Fminus i (Matrix.mulVec inst.T x i) ≤ pi i ∧
                pi i ≤ -(inst.qplus i) + inst.qsum i * Fplus i (Matrix.mulVec inst.T x i)) ∧
          η = fun j => ∑ i, pi i * inst.T i j})
    (hfin : ∃ z0 : ℝ,
      sInf ((fun x => ((dotProduct inst.c x : ℝ) : EReal) + Q x) '' inst.K1) = (z0 : EReal))
    (xstar : Fin n1 → ℝ) (hx : xstar ∈ inst.K1) :
    (((dotProduct inst.c xstar : ℝ) : EReal) + Q xstar =
        sInf ((fun x => ((dotProduct inst.c x : ℝ) : EReal) + Q x) '' inst.K1)) ↔
      ∃ (lam : Fin m1 → ℝ) (mu : Fin n1 → ℝ) (pi : Fin m2 → ℝ),
        (∀ j, 0 ≤ mu j) ∧ dotProduct mu xstar = 0 ∧
        (∀ i, -(inst.qplus i) + inst.qsum i * Fminus i (Matrix.mulVec inst.T xstar i) ≤ pi i ∧
              pi i ≤ -(inst.qplus i) + inst.qsum i * Fplus i (Matrix.mulVec inst.T xstar i)) ∧
        (fun j => -inst.c j + Matrix.mulVec (Matrix.transpose inst.A) lam j + mu j -
            ∑ i, pi i * inst.T i j) = 0 := by sorry

end StochasticProg.Recourse
