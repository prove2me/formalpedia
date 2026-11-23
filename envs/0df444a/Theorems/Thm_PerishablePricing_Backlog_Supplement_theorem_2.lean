-- Prove2me | Theorems.Thm_PerishablePricing_Backlog_Supplement_theorem_2
-- name    : PerishablePricing.Backlog.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:02:14.606801+00:00
-- url     : https://prove2.me/theorems/22e6b255-01eb-47ba-a039-19fbc7d9570f
-- title:
--   Theorem 2 (corrected: off-state sign), p. 293 — full lost-sales structure and demand-range degeneracy
-- statement:
--   Consider the zero-lead-time lost-sales model over either source carrier $\mathbb F\in\{\mathbb R,\mathbb Z\}$, with any finite lifetime $l\ge1$, the §3 demand and cost assumptions, and $h^++h^-\ge\gamma c$. Suppose its carrier versions of (C1) and (C2) hold. Necessarily $\underline d=\bar d$. In each carrier, $f_t$, $g_t(\cdot\mid\varepsilon)$ and $\varphi_t(\cdot\mid\varepsilon)$ are L♮-concave on $\mathcal V^+_{l-1,l-1}$, $\mathcal V^+_{l+1,l}$ and $\mathcal V^+_{l+2,l}$, respectively, leaving $d,a$ unrestricted in the joint functions. At points where the largest optimal order/demand pairs exist, both components are nondecreasing in $s$, the price is nonincreasing, and
--
--   $$s_{lt}(s+\omega e)\le s_{lt}(s)+\omega,\qquad
--   d_t(s+\omega e)\le d_t(s)+\omega\quad(\omega\in\mathbb F_+).$$
--
--   For every fixed $\varepsilon\in\mathbb F$, largest optimal depletions are nondecreasing jointly in $(s,s_l,d)$ and satisfy
--
--   $$a_t(s+\omega e,s_l+\omega,d+\omega\mid\varepsilon)
--   \le a_t(s,s_l,d\mid\varepsilon)+\omega\quad(\omega\in\mathbb F_+).$$
--
--   Both halves include every policy conclusion imported from Theorem 1, including (7) and (8), and use their own full, unbounded feasible-action supremums. The discrete half is an integer Bellman recursion, not the real recursion evaluated at integer initial states. The theorem is an independent companion of the referenced backlogging goal.
--
--   **Formalization Note** For the integer carrier, expected-demand endpoints and noise are integer, so additive realized demand is integer; prices, costs and profit remain real. Conditions (C1) and (C2) use ordinary ambient derivatives of the actual price/CDF at integer decisions, with existence and nonzero price derivative stated where used. This single-carrier convention excludes fractional-mean/mixed-carrier demand choices; it follows the source's explicit real/integer carrier convention rather than claiming a theorem for an arbitrary discrete price grid. C2 is tested only where survival is positive, including below support, and CDF jumps are not smoothed. The real half retains unrestricted real choices and its original noise hypotheses. Time counts periods to go, with terminal value $f_0=0$. Largest maximizers are hypotheses at compared points. The source's missing conditional-noise argument of $g_t$ is restored from (5). The off-state extension is $-\infty$, correcting the printed $+\infty$ sign; the lifetime-one newsvendor boundary is explicit. No Assumption 1, backlog-only cost bound, order cap or integrability premise is added.
--
--   Differences from the source:
--   - reading: (C2) and the derivative-based elasticity quotient → the same hazard-domain reading as in Proposition 3, with existence of the derivatives where used; reason: zero survival probability does not define a hazard rate; points below support are still included
--   - generalization: the full conditional structural conclusion → the same full conclusion together with $\underline d=\bar d$; reason: the demand assumptions and (C2) exclude every positive-width interval, as verified separately without theorem stubs
--   - generalization: $f_t$ for decision periods $t=1,\ldots,T$ → also the terminal function $f_0=0$ in periods-to-go time; reason: a constant terminal function is L♮-concave and the statement specializes to every decision period
--   - reading: the optimal decisions and $g_t$ without a printed noise argument → largest maximizers as hypotheses at the compared points and $g_t$ with noise fixed; reason: Lemma 3 explicitly assumes existence and (5) is conditional on the realized noise
--   - encoding: lifetime $l=1$ reduces to the lost-sales newsvendor (p. 288) → `L = 0` has no old inventory, no carried inventory, and all stock $s_l$ is depleted; reason: the source explicitly includes this boundary; defining empty-state coordinates this way preserves that instance
--   - correction: the modified profit is $+\infty$ off the feasible state space on p. 290 → real values are used only on the feasible state space, representing its $-\infty$ extension; reason: maximization and L♮-concavity require $-\infty$, as seen from (4) and Definition 1; no in-state value changes
--   - reading: continuous and discrete decision variables/demand (p. 285), with the real/integer carrier convention (p. 287) → two complete universally quantified Bellman/policy conjunctions: real and integer, with integer expected-demand endpoints and additive noise for the latter, and ordinary derivative C1/C2 tests at its integer decisions; reason: the integer state must close under (1) and (3); integer d makes integer demand equivalent to integer noise. Fractional-mean/mixed-carrier models are not the F=Z instance, and all real-case domains are preserved
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, https://doi.org/10.1287/opre.2014.1261, Theorem 2, (C1)–(C2), cost assumption p. 293 (PDF 11); Theorem 1 (7)–(8), p. 291 (PDF 9); (3)–(6), p. 290 (PDF 8)

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_Supplement_LostSalesModel
import Definitions.Def_PerishablePricing_Backlog_Supplement_IntegerLostSalesModel

namespace PerishablePricing.Backlog.Supplement

/-- Every clause of Theorem 2 (including its reference to (7),(8)), together with
the obstruction to a nondegenerate pricing interval under its printed assumptions. -/
theorem theorem_2 :
    (∀ {L : ℕ} (M : LostSalesModel L),
      M.toDemandData.C1 → M.toDemandData.C2 →
    M.dlo = M.dhi ∧
    (∀ n : ℕ, LNatConcaveOn (Vplus L L) (M.f n)) ∧
    (∀ (n : ℕ) (ε : ℝ), LNatConcaveOn (Vplus (L + 2) (L + 1)) (M.gJoint n ε)) ∧
    (∀ (n : ℕ) (ε : ℝ), LNatConcaveOn (Vplus (L + 3) (L + 1)) (M.phiJoint n ε)) ∧
    (∀ (n : ℕ) (s s' : Fin L → ℝ) (S D S' D' : ℝ),
      s ∈ LostSalesModel.stateSpace L → s' ∈ LostSalesModel.stateSpace L → s ≤ s' →
      M.IsLargestOptOrder n s S D → M.IsLargestOptOrder n s' S' D' →
      S ≤ S' ∧ D ≤ D' ∧ M.P D' ≤ M.P D) ∧
    (∀ (n : ℕ) (s : Fin L → ℝ) (ω S D S' D' : ℝ),
      s ∈ LostSalesModel.stateSpace L → 0 ≤ ω →
      M.IsLargestOptOrder n s S D → M.IsLargestOptOrder n (s + ω • (1 : Fin L → ℝ)) S' D' →
      S' ≤ S + ω ∧ D' ≤ D + ω) ∧
    (∀ (n : ℕ) (ε : ℝ) (s s' : Fin L → ℝ) (sl sl' d d' a a' : ℝ),
      s ∈ LostSalesModel.stateSpace L → LostSalesModel.sLast s ≤ sl →
      s' ∈ LostSalesModel.stateSpace L → LostSalesModel.sLast s' ≤ sl' →
      s ≤ s' → sl ≤ sl' → d ≤ d' →
      M.IsLargestOptDepletion n s sl d ε a → M.IsLargestOptDepletion n s' sl' d' ε a' →
      a ≤ a') ∧
    (∀ (n : ℕ) (ε : ℝ) (s : Fin L → ℝ) (sl d ω a a' : ℝ),
      s ∈ LostSalesModel.stateSpace L → LostSalesModel.sLast s ≤ sl → 0 ≤ ω →
      M.IsLargestOptDepletion n s sl d ε a →
      M.IsLargestOptDepletion n (s + ω • (1 : Fin L → ℝ)) (sl + ω) (d + ω) ε a' →
      a' ≤ a + ω)
    ) ∧
    (∀ {L : ℕ} (M : IntegerLostSalesModel L),
      M.toIntegerDemandData.C1 → M.toIntegerDemandData.C2 →
    M.lower = M.upper ∧
    (∀ n : ℕ, LNatConcaveOnZ (VplusZ L L) (M.f n)) ∧
    (∀ (n : ℕ) (ε : ℤ), LNatConcaveOnZ (VplusZ (L + 2) (L + 1)) (M.gJoint n ε)) ∧
    (∀ (n : ℕ) (ε : ℤ), LNatConcaveOnZ (VplusZ (L + 3) (L + 1)) (M.phiJoint n ε)) ∧
    (∀ (n : ℕ) (s s' : Fin L → ℤ) (S D S' D' : ℤ),
      s ∈ IntegerLostSalesModel.stateSpace L → s' ∈ IntegerLostSalesModel.stateSpace L → s ≤ s' →
      M.IsLargestOptOrder n s S D → M.IsLargestOptOrder n s' S' D' →
      S ≤ S' ∧ D ≤ D' ∧ M.P (D' : ℝ) ≤ M.P (D : ℝ)) ∧
    (∀ (n : ℕ) (s : Fin L → ℤ) (ω S D S' D' : ℤ),
      s ∈ IntegerLostSalesModel.stateSpace L → 0 ≤ ω →
      M.IsLargestOptOrder n s S D → M.IsLargestOptOrder n (s + ω • (1 : Fin L → ℤ)) S' D' →
      S' ≤ S + ω ∧ D' ≤ D + ω) ∧
    (∀ (n : ℕ) (ε : ℤ) (s s' : Fin L → ℤ) (sl sl' d d' a a' : ℤ),
      s ∈ IntegerLostSalesModel.stateSpace L → IntegerLostSalesModel.sLast s ≤ sl →
      s' ∈ IntegerLostSalesModel.stateSpace L → IntegerLostSalesModel.sLast s' ≤ sl' →
      s ≤ s' → sl ≤ sl' → d ≤ d' →
      M.IsLargestOptDepletion n s sl d ε a → M.IsLargestOptDepletion n s' sl' d' ε a' →
      a ≤ a') ∧
    (∀ (n : ℕ) (ε : ℤ) (s : Fin L → ℤ) (sl d ω a a' : ℤ),
      s ∈ IntegerLostSalesModel.stateSpace L → IntegerLostSalesModel.sLast s ≤ sl → 0 ≤ ω →
      M.IsLargestOptDepletion n s sl d ε a →
      M.IsLargestOptDepletion n (s + ω • (1 : Fin L → ℤ)) (sl + ω) (d + ω) ε a' →
      a' ≤ a + ω)
    ) := by sorry

end PerishablePricing.Backlog.Supplement
