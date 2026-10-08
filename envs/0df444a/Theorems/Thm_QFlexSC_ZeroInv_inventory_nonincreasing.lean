-- Prove2me | Theorems.Thm_QFlexSC_ZeroInv_inventory_nonincreasing
-- name    : QFlexSC.ZeroInv.inventory_nonincreasing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:54.478984+00:00
-- url     : https://prove2.me/theorems/3cd83ac7-92da-4287-b9aa-f043d1f4225d
-- title:
--   Appendix 1, proof of Proposition 2, p. 108 — under (d), r_0(t) ≤ f_0(t), so inventory is non-increasing
-- statement:
--   Consider a flex node running the Minimum Commitment (MC) policy (21)–(23). Assume the standing conditions $\alpha^{in}_q, \alpha^{out}_q \ge 0$ and $0 \le \omega^{in}_q, \omega^{out}_q \le 1$ ($q \ge 1$), that all release quantities are nonnegative, $f_j(t) \ge 0$, that the release schedules obey the output IR constraints (6), and that the input profile dominates the output profile componentwise (condition (d) of Proposition 2):
--   $$A^{out}_j \le A^{in}_j \quad\text{and}\quad \Omega^{out}_j \le \Omega^{in}_j \qquad (j \ge 1).$$
--   Let the run start from $I(0) \ge 0$ and the lot-for-lot schedule $r(0) = f(0)$. Then for every $t \ge 1$
--   $$r_0(t) \le f_0(t) \qquad\text{and hence}\qquad I(t) = I(t-1) + r_0(t) - f_0(t) \le I(t-1).$$
--
--   Together with the coverage property $I(t) \ge 0$, this gives the first part of Proposition 2: inventory that starts at zero stays at zero.
--
--   **Formalization Note.** The paper derives $r_0(t) \le f_0(t)$ from its formula (33), whose maximum over $k \ge 0$ reaches periods before the start of a run; here the claim is stated directly for a run started at period $0$. Two hypotheses are added and disclosed: $f \ge 0$ (the paper's quantities are "measured in end-item equivalents"; the argument multiplies an inequality between flexibility ratios by $f_k$), and the initial state $r(0) = f(0)$, $I(0) \ge 0$ (the paper states no start; with $r_1(0)$ arbitrarily large, $r_0(1) \ge (1-\omega^{in}_1) r_1(0)$ exceeds $f_0(1)$). Parameter index $0$ is unused.
-- source:
--   Tsay & Lovejoy, Quantity flexibility contracts and supply chain performance, MSOM 1(2) (1999), p. 108, Appendix 1, proof of Proposition 2

import Mathlib
import Definitions.Def_QFlexSC_ZeroInv_Model

namespace QFlexSC.ZeroInv

theorem inventory_nonincreasing (P : QFParams) (f : ℕ → ℕ → ℝ) (I₀ : ℝ) (r₀ : ℕ → ℝ)
    (hstd : ∀ q, 1 ≤ q → 0 ≤ P.αin q ∧ 0 ≤ P.αout q ∧ 0 ≤ P.ωin q ∧ P.ωin q ≤ 1 ∧
      0 ≤ P.ωout q ∧ P.ωout q ≤ 1)
    (hf : ∀ t j, 0 ≤ f t j)
    (hIR : IROut P f)
    (hI₀ : 0 ≤ I₀)
    (hr₀ : r₀ = f 0)
    (hd : ∀ j, 1 ≤ j → Acum P.αout j ≤ Acum P.αin j ∧ Ωcum P.ωout j ≤ Ωcum P.ωin j) :
    ∀ t : ℕ, 1 ≤ t →
      sched P I₀ r₀ f t 0 ≤ f t 0 ∧ inv P I₀ r₀ f t ≤ inv P I₀ r₀ f (t - 1) := by sorry

end QFlexSC.ZeroInv
