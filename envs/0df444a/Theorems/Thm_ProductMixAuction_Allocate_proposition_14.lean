-- Prove2me | Theorems.Thm_ProductMixAuction_Allocate_proposition_14
-- name    : ProductMixAuction.Allocate.proposition_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:34.669986+00:00
-- url     : https://prove2.me/theorems/388f23bd-f41f-4962-b5d6-6455cacd8a65
-- title:
--   Proposition 14, p. 21 — after a shift by |ε| < 1/4, r is demanded at some p ± εe^S, and SFM on the Lyapunov function finds such a price
-- statement:
--   Let $\mathcal A$ be an allocation problem with integral bids, integral price $p$ and residual supply $r$, and fix $\varepsilon$ with $|\varepsilon|<\tfrac14$, a good $i\in[n]$ and a bidder $j$. Shift all bids of bidder $j$ by $\varepsilon e^i$ and let $\mathcal B'$ be the resulting aggregate bid list. Let $g(q)=f_{\mathcal B'}(q)+\sum_{i\in[n]}r_iq_i$ be the Lyapunov function of $\mathcal B'$ and $r$, and for $S\subseteq[n]$ let
--   $$h^+(S)=g(p+|\varepsilon|e^S)-g(p),\qquad h^-(S)=g(p-|\varepsilon|e^S)-g(p).$$
--   Then:
--
--   1. there is a price $p^\varepsilon\in\{p\pm\varepsilon e^S:\ S\subseteq[n]\}$ at which $r$ is demanded by $\mathcal B'$;
--   2. $h^+$ and $h^-$ are submodular set functions, and for any minimisers $S^+$ of $h^+$ and $S^-$ of $h^-$, $r$ is demanded by $\mathcal B'$ at whichever of $p+|\varepsilon|e^{S^+}$ and $p-|\varepsilon|e^{S^-}$ has the smaller value of $g$ (at either, in case of a tie).
--
--   Part 2 is the formal content of "we can determine $p^\varepsilon$ using submodular minimisation on the Lyapunov function": two calls to a submodular-minimisation oracle locate a price at which the shifted market still clears the residual supply.
--
--   Differences from the source:
--   - reading: Proposition 14 states no integrality → integral bids and integral price p; reason: the shifting paragraph (p. 21) supposes all bids integral, and the proof uses that integral bids have a surplus gap of at least 1 at integral prices
--   - reading: 'shift all bids of bidder j's in ℬ by ε' → the shift is εeⁱ for a good i ∈ [n]; reason: the shifting paragraph (p. 21) shifts 'in the direction of i by adding εeⁱ'; the proof uses u²[ε,i] (p. 37)
--   - reading: 'We can determine p^ε using submodular minimisation on the Lyapunov function g' → h⁺, h⁻ are submodular and r is demanded at the better of p + |ε|e^{S⁺}, p − |ε|e^{S⁻} for any minimisers S^±; reason: this is the procedure of the proof (p. 38), the one Algorithm 5 runs
--   - reading: h⁻(S) := g(p + εe^S) − g(p) (p. 38, identical to h⁺) → h⁻(S) = g(p − |ε|e^S) − g(p); reason: the candidate set p ± εe^S requires the minus sign; the printed line repeats h⁺
-- source:
--   Baldwin, Goldberg, Klemperer, Lock, Solving Strong-Substitutes Product-Mix Auctions, arXiv:1909.07313v3, p. 21, Proposition 14; proof pp. 36–38

import Mathlib
import Definitions.Def_ProductMixAuction_Allocate_Algorithm

namespace ProductMixAuction.Allocate

theorem proposition_14 {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J] (A : AllocProblem n J)
    (hA : IsAllocProblem A)
    (hbint : ∀ j, ∀ b ∈ A.B j, ∀ k, ∃ z : ℤ, b.v k = z)
    (hpint : ∀ i, ∃ z : ℤ, A.p i = z)
    (ε : ℝ) (hε : |ε| < 1 / 4) (i : Fin n) (j : J) :
    let B' := aggregate (shiftList A.B j i.succ ε)
    let g := gLyap B' A.r
    -- the residual supply is demanded by `B'` at some `p ± ε e^S`
    (∃ S : Finset (Fin n), ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
        A.r ∈ demand B' (A.p + (s * ε) • indicator S)) ∧
    -- `h⁺`, `h⁻` are submodular, and SFM on them finds such a price
    NonmonotoneSubmod.Shared.Submodular (hPlus B' A.r A.p |ε|) ∧
    NonmonotoneSubmod.Shared.Submodular (hMinus B' A.r A.p |ε|) ∧
    ∀ Sp Sm : Finset (Fin n),
      (∀ S, hPlus B' A.r A.p |ε| Sp ≤ hPlus B' A.r A.p |ε| S) →
      (∀ S, hMinus B' A.r A.p |ε| Sm ≤ hMinus B' A.r A.p |ε| S) →
      (g (A.p + |ε| • indicator Sp) ≤ g (A.p - |ε| • indicator Sm) →
          A.r ∈ demand B' (A.p + |ε| • indicator Sp)) ∧
      (g (A.p - |ε| • indicator Sm) ≤ g (A.p + |ε| • indicator Sp) →
          A.r ∈ demand B' (A.p - |ε| • indicator Sm)) := by sorry

end ProductMixAuction.Allocate
