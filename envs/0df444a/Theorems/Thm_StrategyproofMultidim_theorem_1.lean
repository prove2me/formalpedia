-- Prove2me | Theorems.Thm_StrategyproofMultidim_theorem_1
-- name    : StrategyproofMultidim.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:13:55.296509+00:00
-- url     : https://prove2.me/theorems/4f76e5f8-3843-47c0-a59b-9beb8a8b5e26
-- title:
--   Theorem 1 — one buyer: SP and AS iff posted prices
-- statement:
--   Throughout, $m$ objects are sold to $n$ buyers; buyer $i$ has a valuation vector $v_i=(v_i^k)_k$ with every $v_i^k>0$, a profile $v$ is the $n\times m$ matrix of these vectors, and a mechanism $\mu=(d,p)$ assigns at each profile a decision matrix $d(v)$ ($d_i^k(v)=1$ iff buyer $i$ is sold object $k$) and prices $p_i(v)$; buyer $i$'s utility is $u(\mu_i(v);x)=d_i(v)^{\top}x-p_i(v)$ at true valuation $x$.
--
--   Let $n=1$ and let $\mu$ be a regular mechanism. Then $\mu$ is strategyproof and agent sovereign if and only if there are positive constants $T^k$, $k\in M$, such that for every positive profile $v$ and every object $k$:
--
--   1. $d^k(v)=1$ if $v^k>T^k$ and $d^k(v)=0$ if $v^k<T^k$;
--   2. $p(v)=\sum_{k:\,d^k(v)=1}T^k$.
--
--   That is, with one buyer the SP and AS mechanisms are exactly the per-object posted prices.
--
--   Differences from the source:
--   - reading: for any v ∈ 𝒱, there exist positive real numbers {Tᵏ} such that for all v ∈ 𝒱 → ∃ T : Fin m → ℝ (constants), for all positive v; reason: the quantifier over v is repeated; the thresholds are constants, as the proof constructs them for one buyer
--   - reading: 𝒟: elements of each column sum up to 1 (p.5) → IsFeasible: each column sums to at most 1; reason: p.7 sets 𝒟 = {0,1}ᵐ for one buyer, Theorem 4 assumes selling all objects as a separate hypothesis and §7.2 uses a mechanism that sells nothing; with sums = 1 every mechanism would sell everything. Under the sells-all hypothesis the two readings coincide
--   - generalization: m ≥ 2 and n ≥ 1 (§3, p.5: "Fix any m ≥ 2 and n ≥ 1") → n = 1 and any m : ℕ; reason: covers the paper's range m ≥ 2; for m ≤ 1 the characterization holds as well (m = 0: both sides hold, the price is 0 by regularity (i))
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), Theorem 1, pp.7–8 (PDF pp.8–9)

import Mathlib
import Definitions.Def_StrategyproofMultidim_IsMechanism
import Definitions.Def_StrategyproofMultidim_IsRegular
import Definitions.Def_StrategyproofMultidim_SP
import Definitions.Def_StrategyproofMultidim_AS
import Definitions.Def_StrategyproofMultidim_IsThresholdRep

namespace StrategyproofMultidim

/-- **Theorem 1: one buyer — SP and AS iff fixed posted prices** (pp.7–8).
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), pp.7–8: "Theorem 1. A mechanism μ ∈ Γ_{M,1} if and only if for any v ∈ 𝒱, there exist
positive real numbers {Tᵏ}ₖ∈M such that for all v ∈ 𝒱 and all k ∈ M: (1) dᵏ(v) = 1 if vᵏ > Tᵏ,
0 if vᵏ < Tᵏ, and (2) p(v) = ∑_{k:dᵏ(v)=1} Tᵏ."

For a regular mechanism with a single buyer (`n = 1`), strategyproofness and agent sovereignty
hold if and only if there are constants `Tᵏ` (one per object) that represent the mechanism as in
`IsThresholdRep`: positive, the buyer wins `k` above `Tᵏ` and loses it below, and pays the sum of
the `Tᵏ` of the objects it wins.

**Formalization Note.** The quantifiers are read as "there exist `T` such that for all `v`". The
single buyer is `0 : Fin 1`. -/
theorem theorem_1 {m : ℕ} (μ : Mechanism 1 m) (hM : IsMechanism μ) (hR : IsRegular μ) :
    (SP μ ∧ AS μ) ↔ ∃ T : Fin m → ℝ, IsThresholdRep μ (fun _ k _ => T k) := by sorry

end StrategyproofMultidim
