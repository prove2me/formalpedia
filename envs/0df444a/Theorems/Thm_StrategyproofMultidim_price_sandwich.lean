-- Prove2me | Theorems.Thm_StrategyproofMultidim_price_sandwich
-- name    : StrategyproofMultidim.price_sandwich
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:14:17.085528+00:00
-- url     : https://prove2.me/theorems/1fe13fea-0c6f-42cc-884b-c53d0ff3d6a5
-- title:
--   Price sandwich (4.2) and the taxation principle
-- statement:
--   Throughout, $m$ objects are sold to $n$ buyers; buyer $i$ has a valuation vector $v_i=(v_i^k)_k$ with every $v_i^k>0$, a profile $v$ is the $n\times m$ matrix of these vectors, and a mechanism $\mu=(d,p)$ assigns at each profile a decision matrix $d(v)$ ($d_i^k(v)=1$ iff buyer $i$ is sold object $k$) and prices $p_i(v)$; buyer $i$'s utility is $u(\mu_i(v);x)=d_i(v)^{\top}x-p_i(v)$ at true valuation $x$.
--
--   Let $\mu$ be a strategyproof mechanism, $v$ a positive profile, $i$ a buyer and $v_i'$ a positive report. Then
--   $$v_i^{\top}\big[d_i(v_i',v_{-i})-d_i(v_i,v_{-i})\big]\ \le\ p_i(v_i',v_{-i})-p_i(v_i,v_{-i})\ \le\ v_i'^{\top}\big[d_i(v_i',v_{-i})-d_i(v_i,v_{-i})\big],$$
--   and consequently $d_i(v_i',v_{-i})=d_i(v_i,v_{-i})$ implies $p_i(v_i',v_{-i})=p_i(v_i,v_{-i})$: a buyer's price depends only on its bundle (taxation principle).
--
--   The sandwich is the first step of the threshold characterization of Theorems 1 and 2.
--
--   Differences from the source:
--   - generalization: (4.2) derived for μ ∈ Γ_{M,N} (regular, SP, AS) in the proof of Theorem 2 → only SP is assumed; reason: the inequalities follow from SP alone; the statement specializes to the paper's
--   - generalization: m ≥ 2 and n ≥ 1 (§3, p.5: "Fix any m ≥ 2 and n ≥ 1") → any n, m : ℕ; reason: covers the paper's range; the inequalities follow from SP for every n and m
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), eq. (4.2) and the line after it, p.10 (PDF p.11); (4.1), p.8 (PDF p.9)

import Mathlib
import Definitions.Def_StrategyproofMultidim_SP

namespace StrategyproofMultidim

/-- **The price sandwich (4.2) and the taxation principle** (p.10; (4.1) on p.8).
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.10: "vᵢᵀ[dᵢ(v′ᵢ, v₋ᵢ) − dᵢ(vᵢ, v₋ᵢ)] ≤ pᵢ(v′ᵢ, v₋ᵢ) − pᵢ(vᵢ, v₋ᵢ) ≤
v′ᵢᵀ[dᵢ(v′ᵢ, v₋ᵢ) − dᵢ(vᵢ, v₋ᵢ)]. Therefore, as in case of Theorem 1,
dᵢ(vᵢ, v₋ᵢ) = dᵢ(v′ᵢ, v₋ᵢ) ⟹ pᵢ(v′ᵢ, v₋ᵢ) = pᵢ(vᵢ, v₋ᵢ)."

For a strategyproof mechanism, a positive profile `v`, a buyer `i` and a positive report `x`
(the paper's `v′ᵢ`), with `v′ = (x, v₋ᵢ)`: the change of `i`'s price is squeezed between the
changes of the value of `i`'s bundle measured at `vᵢ` and at `x`; equal bundles have equal
prices.

**Formalization Note.** `vᵢᵀdᵢ(w)` is `bundleValue (μ.q w i) (v i)`. -/
theorem price_sandwich {n m : ℕ} (μ : Mechanism n m) (hSP : SP μ)
    (v : Fin n → Fin m → ℝ) (hv : PosProfile v) (i : Fin n) (x : Fin m → ℝ)
    (hx : ∀ k, 0 < x k) :
    bundleValue (μ.q (Function.update v i x) i) (v i) - bundleValue (μ.q v i) (v i) ≤
        μ.t i (Function.update v i x) - μ.t i v ∧
      μ.t i (Function.update v i x) - μ.t i v ≤
        bundleValue (μ.q (Function.update v i x) i) x - bundleValue (μ.q v i) x ∧
      (μ.q (Function.update v i x) i = μ.q v i →
        μ.t i (Function.update v i x) = μ.t i v) := by sorry

end StrategyproofMultidim
