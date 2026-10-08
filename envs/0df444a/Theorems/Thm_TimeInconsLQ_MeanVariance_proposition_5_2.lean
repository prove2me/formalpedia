-- Prove2me | Theorems.Thm_TimeInconsLQ_MeanVariance_proposition_5_2
-- name    : TimeInconsLQ.MeanVariance.proposition_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:54.237193+00:00
-- url     : https://prove2.me/theorems/b7e56577-29f2-4d18-a31a-dff0215b52df
-- title:
--   Proposition 5.2 — the linear BSDE (5.13) has a unique bounded solution (Γ⁽²⁾, γ⁽²⁾), and γ⁽²⁾ · W is BMO
-- statement:
--   In the market of §5 ($r$ deterministic and bounded, $\theta$ progressive and essentially bounded, $\mu_1\ge0$), let $(M,U)\in L^\infty_{\mathcal F}(0,T;\mathbb R)\times L^2_{\mathcal F}(0,T;\mathbb R^d)$ solve the BSDE (5.8) with $M\ge c$ for some constant $c>0$, and let $\Gamma_t=-\mu_2e^{\int_t^Tr_s\,ds}$. Consider
--   $$d\Gamma^{(2)}_t=-\Big[r_t\Gamma^{(2)}_t-\Big(\theta_t+\frac{U_t}{M_t}\Big)'\gamma^{(2)}_t-\Big(|\theta_t|^2+\frac{U_t'\theta_t}{M_t}\Big)\Gamma_t\Big]dt+(\gamma^{(2)}_t)'\,dW_t,\qquad\Gamma^{(2)}_T=-\mu_2. \tag{5.13}$$
--   Then:
--
--   1. (5.13) has a solution $(\Gamma^{(2)},\gamma^{(2)})\in L^\infty_{\mathcal F}(0,T;\mathbb R)\times L^2_{\mathcal F}(0,T;\mathbb R^d)$;
--   2. any two such solutions coincide ($\Gamma^{(2)}_t$ a.s. for every $t$, $\gamma^{(2)}$ $ds\otimes dP$-a.e.);
--   3. for every such solution, $\gamma^{(2)}\cdot W$ is a BMO martingale.
--
--   $(\Gamma^{(2)},\gamma^{(2)})$ supplies the intercept $\beta$ of the equilibrium feedback (5.14).
--
--   **Formalization Note.** The paper's hypothesis "With M, U … obtained" is the solution class of Proposition 5.1; the BMO property of $U\cdot W$ is not assumed (it follows from that class by Proposition 5.1). Uniqueness is read up to modification / $ds\otimes dP$-null sets.
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, p. 19, Proposition 5.2, BSDE (5.13)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_MeanVariance_Model
import Definitions.Def_TimeInconsLQ_MeanVariance_Market

namespace TimeInconsLQ.MeanVariance

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

/-- Proposition 5.2 (p. 19). Given a solution `(M, U)` of (5.8) in the class of Proposition 5.1,
the BSDE (5.13) has a solution `(Γ⁽²⁾, γ⁽²⁾) ∈ L^∞_𝓕(0, T; ℝ) × L²_𝓕(0, T; ℝᵈ)`; any two such
solutions agree (`Γ⁽²⁾` at every time almost surely, `γ⁽²⁾` `ds ⊗ dP`-a.e.); and for every such
solution `γ⁽²⁾ · W` is a BMO martingale. -/
theorem proposition_5_2 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (mk : Market Ω d)
    (hmk : mk.Standing)
    (M : ℝ≥0 → Ω → ℝ) (U : ℝ≥0 → Ω → Fin d → ℝ) (hMU : mk.Class58 M U) :
    (∃ Γ2 γ2, mk.Class513 M U Γ2 γ2) ∧
    (∀ Γ2 γ2 Γ2' γ2', mk.Class513 M U Γ2 γ2 → mk.Class513 M U Γ2' γ2' →
      (∀ t ≤ mk.T, Γ2 t =ᵐ[mk.P] Γ2' t) ∧
      ∀ᵐ q ∂((volume.restrict (Set.Icc (0 : ℝ) mk.T)).prod mk.P),
        γ2 q.1.toNNReal q.2 = γ2' q.1.toNNReal q.2) ∧
    (∀ Γ2 γ2, mk.Class513 M U Γ2 γ2 → IsBMO mk.filt mk.P mk.T γ2) := by sorry

end TimeInconsLQ.MeanVariance
