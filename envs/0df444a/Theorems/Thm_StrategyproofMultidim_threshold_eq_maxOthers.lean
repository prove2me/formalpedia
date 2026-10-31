-- Prove2me | Theorems.Thm_StrategyproofMultidim_threshold_eq_maxOthers
-- name    : StrategyproofMultidim.threshold_eq_maxOthers
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:14:07.495094+00:00
-- url     : https://prove2.me/theorems/c054f378-03e8-4f45-a206-dbaae5f6a947
-- title:
--   Necessity in Theorem 4 — thresholds equal the highest competing bid (corrected: whole profiles)
-- statement:
--   Throughout, $m$ objects are sold to $n$ buyers; buyer $i$ has a valuation vector $v_i=(v_i^k)_k$ with every $v_i^k>0$, a profile $v$ is the $n\times m$ matrix of these vectors, and a mechanism $\mu=(d,p)$ assigns at each profile a decision matrix $d(v)$ ($d_i^k(v)=1$ iff buyer $i$ is sold object $k$) and prices $p_i(v)$; buyer $i$'s utility is $u(\mu_i(v);x)=d_i(v)^{\top}x-p_i(v)$ at true valuation $x$.
--
--   Let $n\ge 2$ and let $\mu$ be a regular, strategyproof, agent-sovereign mechanism that satisfies anonymity in welfare and sells every object at every profile. Then every threshold representation $T$ of $\mu$ satisfies, at every positive profile $v$, for every buyer $i$ and object $k$,
--   $$T_i^k(v_{-i})=\max_{j\neq i}v_j^k .$$
--
--   Hence each object goes to a highest bidder: the mechanism is efficient.
--
--   Differences from the source:
--   - correction: Tᵏ(z) = maxₜ zₜ for z ∈ ℝⁿ⁻¹₊₊, the column k of v₋ᵢ (via Theorem 3 and Proposition 2) → Tᵢᵏ evaluated on the whole profile v (all columns of v₋ᵢ) equals max_{j≠i} vⱼᵏ; reason: Theorem 3 (continuous ⟹ thresholds depend on column k only) is false (the Proposition 2 counterexample), so T may a priori depend on other columns; the statement on whole profiles shows it does not
--   - generalization: μ ∈ Γ̄_{M,N} (continuous, Definition 4) → μ in Γ_{M,N}: IsMechanism, IsRegular, SP, AS; no continuity hypothesis; reason: Γ̄ ⊆ Γ, so the statement specializes to the paper's under any reading of Definition 4; the result holds without continuity
--   - encoding: z ∈ ℝⁿ⁻¹₊₊ and maxₜ zₜ (meaningful for n ≥ 2 only) → 2 ≤ n; maxOthers v i k (real supremum over j ≠ i); reason: excludes the undefined case n = 1; for n ≥ 2 the supremum over a finite nonempty set is the maximum
--   - encoding: Tᵢᵏ : Πⱼ≠ᵢVⱼ → ℝ₊₊, the thresholds of Theorem 2 → any T : Fin n → Fin m → profile → ℝ with IsThresholdRep μ T (ignores row i, positive at positive profiles); reason: a function of v₋ᵢ is a function of the profile that ignores row i; the paper's T is such a representation
--   - reading: 𝒟: elements of each column sum up to 1 (p.5) → IsFeasible: each column sums to at most 1; reason: p.7 sets 𝒟 = {0,1}ᵐ for one buyer, Theorem 4 assumes selling all objects as a separate hypothesis and §7.2 uses a mechanism that sells nothing; with sums = 1 every mechanism would sell everything. Under the sells-all hypothesis the two readings coincide
--   - generalization: m ≥ 2 and n ≥ 1 (§3, p.5: "Fix any m ≥ 2 and n ≥ 1") → 2 ≤ n (the encoding above) and any m : ℕ; reason: covers the paper's range m ≥ 2; the argument is per object and does not use m ≥ 2
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), proof of Theorem 4 (necessity), last display of §7.1, pp.23–24 (PDF pp.24–25)

import Mathlib
import Definitions.Def_StrategyproofMultidim_IsMechanism
import Definitions.Def_StrategyproofMultidim_IsRegular
import Definitions.Def_StrategyproofMultidim_SP
import Definitions.Def_StrategyproofMultidim_AS
import Definitions.Def_StrategyproofMultidim_AN
import Definitions.Def_StrategyproofMultidim_SellsAll
import Definitions.Def_StrategyproofMultidim_IsThresholdRep
import Definitions.Def_StrategyproofMultidim_maxOthers

namespace StrategyproofMultidim

/-- **Necessity of Theorem 4: thresholds are the highest competing bid** (pp.23–24, last
display of §7.1).
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.23: "Thus, we can infer that for all z ∈ ⋃ⁿ⁻¹ₜ₌₁ Hₓᵗ, Tᵏ(z) = maxₜ zₜ = x. Now, since x
was arbitrarily chosen, it follows that: Tᵏ(z) = maxₜ zₜ, for all z ∈ ℝⁿ⁻¹₊₊," (p.24: "and so, the
result follows.")

Let `n ≥ 2`. For a mechanism in `Γ_{M,N}` that satisfies AN and sells every object at every
profile, every threshold representation `T` satisfies `Tᵢᵏ(v₋ᵢ) = max_{j≠i} vⱼᵏ` at every
positive profile.

**Formalization Note.** The paper's `z` is column `k` of `v₋ᵢ`; here `T` is a function of the
whole `v₋ᵢ`, and the conclusion shows it depends on column `k` only. Continuity is not assumed. -/
theorem threshold_eq_maxOthers {n m : ℕ} (hn : 2 ≤ n) (μ : Mechanism n m) (hM : IsMechanism μ) (hR : IsRegular μ) (hSP : SP μ) (hAS : AS μ)
    (hAN : AN μ) (hSell : SellsAll μ)
    (T : Fin n → Fin m → (Fin n → Fin m → ℝ) → ℝ) (hT : IsThresholdRep μ T)
    (v : Fin n → Fin m → ℝ) (hv : PosProfile v) (i : Fin n) (k : Fin m) :
    T i k v = maxOthers v i k := by sorry

end StrategyproofMultidim
