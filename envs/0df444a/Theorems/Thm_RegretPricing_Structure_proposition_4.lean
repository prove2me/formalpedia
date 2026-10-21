-- Prove2me | Theorems.Thm_RegretPricing_Structure_proposition_4
-- name    : RegretPricing.Structure.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:44.940973+00:00
-- url     : https://prove2.me/theorems/d6d976d7-69a0-4d94-9c88-e33ecebfcac7
-- title:
--   Proposition 4, p. 10 — ΔU_t(x) and the regretful price p̂_t(x) increase in time-to-go t and decrease in remaining inventory x
-- statement:
--   Let the willingness-to-pay law have support $[a,b]$, $0\le a<b<\infty$, a density continuous on $[a,b]$, and an increasing failure rate. Let $\alpha,\beta\in[0,1]$ be the overpricing and underpricing parameters, let the arrival probability satisfy $0\le\lambda\le1/2$, and assume the regularity condition $\hat m(z,\alpha,\beta)\le 0$ of p. 6, i.e. that $z\mapsto\max_p\hat\pi(p,z)$ is non-increasing on $[0,b]$. Let $U_t(x)$ be the value-to-go (10) and $\Delta U_t(x)=U_t(x)-U_t(x-1)$. Then, for all $t\ge0$ and $x\ge1$:
--
--   1. $\Delta U_t(x)\le\Delta U_{t+1}(x)$ and $\Delta U_t(x+1)\le\Delta U_t(x)$;
--   2. the price problem of (10), $\max_p\hat\pi(p,\Delta U_t(x))$, has exactly one solution $\hat p_{t+1}(x)$;
--   3. $$\hat p_{t+1}(x)\le\hat p_{t+2}(x)\qquad\text{and}\qquad\hat p_{t+1}(x+1)\le\hat p_{t+1}(x).$$
--
--   In words: the regretful seller's marginal value of inventory and her price both increase with the time-to-go and decrease with the remaining inventory. This is the paper's structural result for the dynamic problem.
--
--   **Formalization Note.** "Increases"/"decreases" are weak (p. 4). Time-to-go is indexed by $\mathbb N$; $\hat p_{t}(x)$ is a maximizer of $\hat\pi(\cdot,\Delta U_{t-1}(x))$ (p. 21), hence the shift by one in clauses 2–3, which quantify over all maximizers. Clause 2 makes explicit the page's presupposition "the solution to (10)", so that clause 3 is not vacuous. "For any bias parameters" is read as the paper's standing range $\alpha,\beta\in[0,1]$ (p. 5). The regularity condition is about the single-period value; the inventory cap $x\le c$ is dropped; continuity of the density is added.
-- source:
--   Li & Liu, Managerial regret and inventory pricing, accepted manuscript (Management Science, forthcoming; SSRN 3726966), p. 10 (PDF 10), Proposition 4

import Mathlib
import Definitions.Def_RegretPricing_Structure_Model

namespace RegretPricing.Structure

/-- Proposition 4, p. 10: for bias parameters `α, β ∈ [0, 1]` and `λ ≤ 1/2`, under the
regularity assumption `m̂ ≤ 0` (p. 6),
(a) `ΔU_t(x)` increases in the time-to-go `t` and decreases in the remaining inventory `x`;
(b) the solution `p̂_t(x)` of (10), a maximizer of `π̂(·, ΔU_{t-1}(x))`, exists, is unique,
increases in `t` and decreases in `x`. -/
theorem proposition_4 (D : WTP) (hD : D.Standing) (hIFR : D.IFR) (α β lam : ℝ)
    (hα : 0 ≤ α ∧ α ≤ 1) (hβ : 0 ≤ β ∧ β ≤ 1) (hlam : 0 ≤ lam ∧ lam ≤ 1 / 2)
    (hm : AntitoneOn (regretValue D α β) (Set.Icc 0 D.b)) :
    (∀ t x : ℕ, 1 ≤ x → dU D α β lam t x ≤ dU D α β lam (t + 1) x) ∧
      (∀ t x : ℕ, 1 ≤ x → dU D α β lam t (x + 1) ≤ dU D α β lam t x) ∧
      (∀ t x : ℕ, 1 ≤ x → ∃! p, IsRegretPrice D α β (dU D α β lam t x) p) ∧
      (∀ t x : ℕ, 1 ≤ x → ∀ p p', IsRegretPrice D α β (dU D α β lam t x) p →
        IsRegretPrice D α β (dU D α β lam (t + 1) x) p' → p ≤ p') ∧
      (∀ t x : ℕ, 1 ≤ x → ∀ p p', IsRegretPrice D α β (dU D α β lam t (x + 1)) p →
        IsRegretPrice D α β (dU D α β lam t x) p' → p ≤ p') := by sorry

end RegretPricing.Structure
