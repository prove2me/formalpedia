-- Prove2me | Theorems.Thm_PeskirShiryaev_AmericanPut_time_continuity
-- name    : PeskirShiryaev.AmericanPut.time_continuity
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:26:28.811357+00:00
-- url     : https://prove2.me/theorems/a071da33-bb32-4202-b8de-4f5b5ce5a3c5
-- title:
--   Eq. (25.2.14) — time-continuity estimate
-- statement:
--   In the geometric Brownian American put model, fix $0\le t_1<t_2\le T$ and $x>0$. Let $\tau_1$ be any optimal stopping time for $V(t_1,x)$, and put $\tau_2=\tau_1\wedge(T-t_2)$. With $S_s=\exp(\sigma B_s+(r-\sigma^2/2)s)$ and $L(\delta)=E[1-\inf_{0\le s\le\delta}S_s]$,
--   $$0\le V(t_1,x)-V(t_2,x)\le xE[S_{\tau_2}]L(t_2-t_1)\le xe^{rT}L(t_2-t_1).$$
--   This is the source's estimate for time continuity of the value function. The intermediate expectation and the final factor $e^{rT}$ are both retained.
--
--   **Formalization Note** Optimality of $\tau_1$ is a hypothesis of this estimate, as in its preceding paragraph; existence and optimality of the boundary hitting rule are a separate milestone. Finding F1 records a gap in the displayed derivation (25.2.13), without altering this statement.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, p. 381 (PDF 397), Eqs. (25.2.12)–(25.2.14)

import Definitions.Def_PeskirShiryaev_AmericanPut_Model

open MeasureTheory ProbabilityTheory

open scoped NNReal ENNReal

namespace PeskirShiryaev.AmericanPut

theorem time_continuity {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (t₁ t₂ x : ℝ) (ht₁ : 0 ≤ t₁) (hlt : t₁ < t₂) (ht₂ : t₂ ≤ M.T)
    (hx : 0 < x) (τ₁ : Ω → ℝ≥0) (hτ₁ : M.Admissible t₁ τ₁)
    (hopt : M.reward x τ₁ = M.value t₁ x) :
    let τ₂ := fun ω => min (τ₁ ω) (M.T - t₂).toNNReal
    let L := M.modulus (t₂ - t₁).toNNReal
    0 ≤ M.value t₁ x - M.value t₂ x ∧
    M.value t₁ x - M.value t₂ x ≤ x * (∫ ω, M.stock 1 (τ₂ ω) ω ∂M.P) * L ∧
    x * (∫ ω, M.stock 1 (τ₂ ω) ω ∂M.P) * L ≤ x * Real.exp (M.r * M.T) * L := by sorry

end PeskirShiryaev.AmericanPut
