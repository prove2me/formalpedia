-- Prove2me | Theorems.Thm_SupplyFlex_SupplierLed_theorem_2
-- name    : SupplyFlex.SupplierLed.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:51:51.422384+00:00
-- url     : https://prove2.me/theorems/b8c2bfbc-541c-44d5-9d37-35ad94f31ff4
-- title:
--   Theorem 2, p. 9 (corrected: w unique only when q* > 0) — the price-only equilibrium: w = rF̄(q*), q = y = q*
-- statement:
--   Consider the price-only game (the guaranteed fraction is fixed at $b = 1$) of a standard model. Let $q^* = \tilde q$, the solution of
--   $$\bar F(q)\left[1 - \frac{q f(q)}{\bar F(q)}\right] = \frac{c + (1-p)s}{r} \qquad (1)$$
--   in $[0, \infty)$, when $c + (1-p)s \le r$, and $q^* = 0$ otherwise. Then:
--   1. there is a subgame-perfect equilibrium with wholesale price $w = r\bar F(q^*)$, order $q = q^*$ and production input $y = q^*$;
--   2. in every subgame-perfect equilibrium the order is $q = q^*$ and the input is $y = q^*$; if $q^* > 0$ the price is $w = r\bar F(q^*)$, and if $q^* = 0$ the price is some $w \ge r$.
--
--   This is the benchmark the supply-flexibility contract is compared with: it gives the buyer's and supplier's profits under the price-only contract.
--
--   **Formalization Note.** The paper states the equilibrium as unique. When $q^* = 0$ every price $w \ge r$ gives both players zero and is an equilibrium price, so uniqueness of $w$ is claimed only for $q^* > 0$. The root $q^*$ is an argument with the hypothesis that it solves (1) (resp. equals $0$).
-- source:
--   Farahani, Dawande, Gurnani & Janakiraman, Better to bend than to break (SSRN 3143238), p. 9, Theorem 2 and eq. (1)

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_SupplyFlex_SupplierLed_Setting

namespace SupplyFlex.SupplierLed

/-- Theorem 2, p. 9 (corrected: the price is unique only when q* > 0). -/
theorem theorem_2 (M : Model) (hM : M.Std) (qstar : ℝ)
    (hqstar : (M.c + (1 - M.p) * M.s ≤ M.r →
        0 ≤ qstar ∧ M.r * G M.f qstar = M.c + (1 - M.p) * M.s) ∧
      (M.r < M.c + (1 - M.p) * M.s → qstar = 0)) :
    (∃ σ : Profile, IsSPE M .priceOnly σ ∧ σ.w = M.r * Fbar M.f qstar ∧
        σ.Q σ.w σ.b = qstar ∧ σ.Y σ.w σ.b qstar = qstar) ∧
    ∀ σ : Profile, IsSPE M .priceOnly σ →
      σ.Q σ.w σ.b = qstar ∧ σ.Y σ.w σ.b qstar = qstar ∧
      (0 < qstar → σ.w = M.r * Fbar M.f qstar) ∧ (qstar = 0 → M.r ≤ σ.w) := by sorry

end SupplyFlex.SupplierLed
