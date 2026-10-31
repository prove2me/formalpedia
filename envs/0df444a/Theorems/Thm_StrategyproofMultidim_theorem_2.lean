-- Prove2me | Theorems.Thm_StrategyproofMultidim_theorem_2
-- name    : StrategyproofMultidim.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:14:20.982785+00:00
-- url     : https://prove2.me/theorems/f28a5aa5-c6f0-4c3c-a9b2-ac002db4faea
-- title:
--   Theorem 2 — SP and AS iff threshold mechanism
-- statement:
--   Throughout, $m$ objects are sold to $n$ buyers; buyer $i$ has a valuation vector $v_i=(v_i^k)_k$ with every $v_i^k>0$, a profile $v$ is the $n\times m$ matrix of these vectors, and a mechanism $\mu=(d,p)$ assigns at each profile a decision matrix $d(v)$ ($d_i^k(v)=1$ iff buyer $i$ is sold object $k$) and prices $p_i(v)$; buyer $i$'s utility is $u(\mu_i(v);x)=d_i(v)^{\top}x-p_i(v)$ at true valuation $x$.
--
--   A regular mechanism $\mu$ is strategyproof and agent sovereign if and only if, for every buyer $i$, there are functions $T_i^k$ of the other buyers' reports $v_{-i}$ with positive values such that for every positive profile $v$ and object $k$:
--
--   1. $d_i^k(v)=1$ if $v_i^k>T_i^k(v_{-i})$ and $d_i^k(v)=0$ if $v_i^k<T_i^k(v_{-i})$;
--   2. $p_i(v)=\sum_{k:\,d_i^k(v)=1}T_i^k(v_{-i})$.
--
--   Every buyer faces, for each object, a personalized price that depends only on the others' reports, and buys exactly the objects worth more than their price.
--
--   Differences from the source:
--   - reading: p_i(v) = Σ over k : dᵏ(v) = 1 → sum over k with dᵢᵏ(v) = 1; reason: the buyer index is missing on the page; dᵢᵏ is meant
--   - encoding: Tᵢᵏ : Πⱼ≠ᵢVⱼ → ℝ₊₊, the thresholds of Theorem 2 → any T : Fin n → Fin m → profile → ℝ with IsThresholdRep μ T (ignores row i, positive at positive profiles); reason: a function of v₋ᵢ is a function of the profile that ignores row i; the paper's T is such a representation
--   - reading: 𝒟: elements of each column sum up to 1 (p.5) → IsFeasible: each column sums to at most 1; reason: p.7 sets 𝒟 = {0,1}ᵐ for one buyer, Theorem 4 assumes selling all objects as a separate hypothesis and §7.2 uses a mechanism that sells nothing; with sums = 1 every mechanism would sell everything. Under the sells-all hypothesis the two readings coincide
--   - generalization: m ≥ 2 and n ≥ 1 (§3, p.5: "Fix any m ≥ 2 and n ≥ 1") → any n, m : ℕ; reason: covers the paper's range; for m ≤ 1 or n = 0 the characterization holds as well
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), Theorem 2, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_StrategyproofMultidim_IsMechanism
import Definitions.Def_StrategyproofMultidim_IsRegular
import Definitions.Def_StrategyproofMultidim_SP
import Definitions.Def_StrategyproofMultidim_AS
import Definitions.Def_StrategyproofMultidim_IsThresholdRep

namespace StrategyproofMultidim

/-- **Theorem 2: SP and AS iff threshold mechanism** (p.10).
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.10: "Theorem 2. A mechanism μ ∈ Γ_{M,N} if and only if for any i ∈ N, there exist
functions {Tᵢᵏ : Πⱼ≠ᵢVⱼ ⟶ ℝ₊₊}ₖ∈M such that for all v ∈ 𝒱 and all k ∈ M: (1) dᵢᵏ(v) = 1 if
vᵢᵏ > Tᵢᵏ(v₋ᵢ), 0 if vᵢᵏ < Tᵢᵏ(v₋ᵢ), and (2) pᵢ(v) = ∑_{k:dᵏ(v)=1} Tᵢᵏ(v₋ᵢ)."

A regular mechanism is strategyproof and agent sovereign if and only if it has a threshold
representation `T` (`IsThresholdRep`): positive thresholds `Tᵢᵏ(v₋ᵢ)` depending only on the other
buyers' reports, buyer `i` wins `k` above `Tᵢᵏ` and loses it below, and pays the sum of the
thresholds of the objects it wins. -/
theorem theorem_2 {n m : ℕ} (μ : Mechanism n m) (hM : IsMechanism μ) (hR : IsRegular μ) :
    (SP μ ∧ AS μ) ↔ ∃ T, IsThresholdRep μ T := by sorry

end StrategyproofMultidim
