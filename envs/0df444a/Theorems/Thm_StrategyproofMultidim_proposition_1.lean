-- Prove2me | Theorems.Thm_StrategyproofMultidim_proposition_1
-- name    : StrategyproofMultidim.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:14:18.75383+00:00
-- url     : https://prove2.me/theorems/d972bce0-8615-4491-9a6c-e8a7f7c60782
-- title:
--   Proposition 1 — a winner of an all-equal column has threshold $x$ (corrected: $n\ge 2$)
-- statement:
--   Throughout, $m$ objects are sold to $n$ buyers; buyer $i$ has a valuation vector $v_i=(v_i^k)_k$ with every $v_i^k>0$, a profile $v$ is the $n\times m$ matrix of these vectors, and a mechanism $\mu=(d,p)$ assigns at each profile a decision matrix $d(v)$ ($d_i^k(v)=1$ iff buyer $i$ is sold object $k$) and prices $p_i(v)$; buyer $i$'s utility is $u(\mu_i(v);x)=d_i(v)^{\top}x-p_i(v)$ at true valuation $x$.
--
--   Let $n\ge 2$ and let $\mu$ be a regular, strategyproof, agent-sovereign mechanism satisfying anonymity in welfare, with threshold representation $T$. Let $x>0$, $k$ an object and $v$ a positive profile in which every buyer reports $x$ for object $k$ ($v^k=x\mathbf 1^n$). If buyer $i$ wins $k$ ($k\in O_i(v)$, the set of objects sold to $i$), then
--   $$T_i^k(v_{-i})=x .$$
--
--   Differences from the source:
--   - correction: any n ≥ 1 → 2 ≤ n; reason: false for n = 1: m = 2 with posted prices T = (1, 1) is regular, SP, AS, continuous and (trivially) AN, and at v = (2, 2) the buyer wins object 1 while T¹ = 1 ≠ 2; the paper's proof needs a second buyer h ≠ i
--   - generalization: μ ∈ Γ̄_{M,N} (continuous, Definition 4) → μ in Γ_{M,N}: IsMechanism, IsRegular, SP, AS; no continuity hypothesis; reason: Γ̄ ⊆ Γ, so the statement specializes to the paper's under any reading of Definition 4; the result holds without continuity
--   - encoding: Tᵢᵏ : Πⱼ≠ᵢVⱼ → ℝ₊₊, the thresholds of Theorem 2 → any T : Fin n → Fin m → profile → ℝ with IsThresholdRep μ T (ignores row i, positive at positive profiles); reason: a function of v₋ᵢ is a function of the profile that ignores row i; the paper's T is such a representation
--   - reading: 𝒟: elements of each column sum up to 1 (p.5) → IsFeasible: each column sums to at most 1; reason: p.7 sets 𝒟 = {0,1}ᵐ for one buyer, Theorem 4 assumes selling all objects as a separate hypothesis and §7.2 uses a mechanism that sells nothing; with sums = 1 every mechanism would sell everything. Under the sells-all hypothesis the two readings coincide
--   - generalization: m ≥ 2 and n ≥ 1 (§3, p.5: "Fix any m ≥ 2 and n ≥ 1") → 2 ≤ n (the correction above) and any m : ℕ; reason: covers the paper's range m ≥ 2; the argument does not use m ≥ 2
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), Proposition 1, p.21 (PDF p.22)

import Mathlib
import Definitions.Def_StrategyproofMultidim_IsMechanism
import Definitions.Def_StrategyproofMultidim_IsRegular
import Definitions.Def_StrategyproofMultidim_SP
import Definitions.Def_StrategyproofMultidim_AS
import Definitions.Def_StrategyproofMultidim_AN
import Definitions.Def_StrategyproofMultidim_IsThresholdRep

namespace StrategyproofMultidim

/-- **Proposition 1 (corrected: n ≥ 2): a winner of an all-equal column pays that bid** (p.21).
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.21: "Proposition 1. If a mechanism μ ∈ Γ̄_{M,N} satisfies AN, then for any x > 0,
k ∈ M and v ∈ 𝒱 such that vᵏ = x1ⁿ; k ∈ Oᵢ(v) ⟹ Tᵢᵏ(v₋ᵢ) = x."

Let `n ≥ 2`. For a mechanism in `Γ_{M,N}` satisfying AN, with threshold representation `T`: if
every buyer reports the same value `x > 0` for object `k` and buyer `i` wins `k`
(`k ∈ Oᵢ(v)`), then buyer `i`'s threshold for `k` is `x`.

**Formalization Note.** The printed statement fails for `n = 1`: posted prices `T = (1, 1)` with
`m = 2` are in `Γ̄`, satisfy AN, and at `v = (2, 2)` the buyer wins object 1 with `T¹ = 1 ≠ 2`.
Continuity is not assumed. -/
theorem proposition_1 {n m : ℕ} (hn : 2 ≤ n) (μ : Mechanism n m) (hM : IsMechanism μ) (hR : IsRegular μ) (hSP : SP μ) (hAS : AS μ) (hAN : AN μ)
    (T : Fin n → Fin m → (Fin n → Fin m → ℝ) → ℝ) (hT : IsThresholdRep μ T)
    (x : ℝ) (hx : 0 < x) (k : Fin m) (v : Fin n → Fin m → ℝ) (hv : PosProfile v)
    (hvk : ∀ t, v t k = x) (i : Fin n) (hi : μ.q v i k = true) :
    T i k v = x := by sorry

end StrategyproofMultidim
