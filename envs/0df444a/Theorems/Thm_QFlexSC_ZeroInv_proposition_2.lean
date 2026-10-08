-- Prove2me | Theorems.Thm_QFlexSC_ZeroInv_proposition_2
-- name    : QFlexSC.ZeroInv.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:02.511117+00:00
-- url     : https://prove2.me/theorems/e3d8b747-f776-461a-ad19-d36dda406428
-- title:
--   Proposition 2, p. 97 — under the MC policy, supply flexibility at least the customer's keeps inventory at zero; equal flexibilities give lot-for-lot
-- statement:
--   Consider a flex node with input QF parameters $(\alpha^{in}_q, \omega^{in}_q)$ and output QF parameters $(\alpha^{out}_q, \omega^{out}_q)$, $q \ge 1$, satisfying the standing assumptions $\alpha^{in}_q, \alpha^{out}_q \ge 0$ and $0 \le \omega^{in}_q, \omega^{out}_q \le 1$, with cumulative flexibilities $1 + A_j = \prod_{q=1}^{j}(1+\alpha_q)$ and $1 - \Omega_j = \prod_{q=1}^{j}(1-\omega_q)$. Suppose that
--
--   1. (a) the release schedules $f(t)$ received in periods $t \ge 0$ are nonnegative and their updates obey the output IR constraints (6);
--   2. (b) the node uses the Minimum Commitment policy (21)–(23) in every period $t \ge 1$;
--   3. (c) $I(0) = 0$, and the run starts lot-for-lot, $r(0) = f(0)$;
--   4. (d) $(A^{in}, \Omega^{in}) \ge (A^{out}, \Omega^{out})$, i.e. $A^{out}_j \le A^{in}_j$ and $\Omega^{out}_j \le \Omega^{in}_j$ for all $j \ge 1$.
--
--   Then the node holds no inventory:
--   $$I(t) = 0 \qquad \text{for all } t \ge 0 .$$
--   Moreover, in the special case $(A^{in}, \Omega^{in}) = (A^{out}, \Omega^{out})$, provided $\omega^{in}_q < 1$ for all $q \ge 1$, the node is a pure lot-for-lot conduit:
--   $$r_j(t) = f_j(t) \qquad \text{for all } j \ge 0,\ t \ge 1 .$$
--
--   The proposition makes precise the claim that inventory at a flex node results from a disparity between input and output flexibility: a node whose supply side is at least as flexible as its customer side can meet every obligation with zero stock, and with matched flexibility it transmits every schedule upstream unaltered.
--
--   **Formalization Note.** Three hypotheses are added to the page's statement and disclosed. (i) $f_j(t) \ge 0$: the paper's quantities are "measured in end-item equivalents", and its proof multiplies an inequality between flexibility ratios by $f_k$. (ii) The start $r(0) = f(0)$: the paper names no initial schedule, and without a condition on it the claim fails (a large $r_1(0)$ forces $r_0(1) \ge (1-\omega^{in}_1) r_1(0) > f_0(1)$). (iii) $\omega^{in}_q < 1$ in the equal case only: the paper's proof divides by $1 - \Omega^{in}_j$; with $\omega^{in}_1 = \omega^{out}_1 = 1$, $\omega^{in}_2 = 0$, $\omega^{out}_2 = 1$ (equal profiles $\Omega_j = 1$), $f_2(0) = 10$, $f_1(1) = 5$, the MC policy gives $r_1(1) \ge 10 \ne f_1(1)$. Constraint (6) is stated with index $j+1$ in place of $j$; the parameter sequences' value at index $0$ is unused; period $0$ is the initial state and the policy acts from period $1$ on.
-- source:
--   Tsay & Lovejoy, Quantity flexibility contracts and supply chain performance, MSOM 1(2) (1999), p. 97, Proposition 2 (proof: Appendix 1, pp. 108–109)

import Mathlib
import Definitions.Def_QFlexSC_ZeroInv_Model

namespace QFlexSC.ZeroInv

theorem proposition_2 (P : QFParams) (f : ℕ → ℕ → ℝ) (I₀ : ℝ) (r₀ : ℕ → ℝ)
    (hstd : ∀ q, 1 ≤ q → 0 ≤ P.αin q ∧ 0 ≤ P.αout q ∧ 0 ≤ P.ωin q ∧ P.ωin q ≤ 1 ∧
      0 ≤ P.ωout q ∧ P.ωout q ≤ 1)
    (hf : ∀ t j, 0 ≤ f t j)
    (ha : IROut P f)
    (hc : I₀ = 0)
    (hr₀ : r₀ = f 0)
    (hd : ∀ j, 1 ≤ j → Acum P.αout j ≤ Acum P.αin j ∧ Ωcum P.ωout j ≤ Ωcum P.ωin j) :
    (∀ t : ℕ, inv P I₀ r₀ f t = 0) ∧
      ((∀ j, 1 ≤ j → Acum P.αin j = Acum P.αout j ∧ Ωcum P.ωin j = Ωcum P.ωout j) →
        (∀ q, 1 ≤ q → P.ωin q < 1) →
        ∀ t : ℕ, 1 ≤ t → ∀ j : ℕ, sched P I₀ r₀ f t j = f t j) := by sorry

end QFlexSC.ZeroInv
