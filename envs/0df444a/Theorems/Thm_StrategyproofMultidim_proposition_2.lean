-- Prove2me | Theorems.Thm_StrategyproofMultidim_proposition_2
-- name    : StrategyproofMultidim.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:14:22.049869+00:00
-- url     : https://prove2.me/theorems/768808e7-c88c-443d-8f09-235fd0b530c0
-- title:
--   Proposition 2 — thresholds are anonymous (corrected: rows of the other buyers, not column k)
-- statement:
--   Throughout, $m$ objects are sold to $n$ buyers; buyer $i$ has a valuation vector $v_i=(v_i^k)_k$ with every $v_i^k>0$, a profile $v$ is the $n\times m$ matrix of these vectors, and a mechanism $\mu=(d,p)$ assigns at each profile a decision matrix $d(v)$ ($d_i^k(v)=1$ iff buyer $i$ is sold object $k$) and prices $p_i(v)$; buyer $i$'s utility is $u(\mu_i(v);x)=d_i(v)^{\top}x-p_i(v)$ at true valuation $x$.
--
--   Let $\mu$ be a regular, strategyproof, agent-sovereign mechanism satisfying anonymity in welfare, with threshold representation $T$ (Theorem 2). Then for every permutation $\pi$ of the buyers, every positive profile $v$, buyer $i$ and object $k$,
--   $$T_{\pi i}^k\big((\pi v)_{-\pi i}\big)=T_i^k(v_{-i}),\qquad \pi v=(v_{\pi^{-1}(t)})_t .$$
--   Equivalently: if the other buyers' valuation rows $\tilde v_{-j}$ are a relabelling of $v_{-i}$, then $T_i^k(v_{-i})=T_j^k(\tilde v_{-j})$.
--
--   Anonymity forces all buyers to face the same threshold function of the others' reports.
--
--   Differences from the source:
--   - correction: vᵏ₋ᵢ = ṽᵏ₋ⱼ (column k of the other buyers agrees) ⟹ Tᵢᵏ(v₋ᵢ) = Tⱼᵏ(ṽ₋ⱼ) → ṽ₋ⱼ a relabelling of v₋ᵢ (whole rows): T (π i) k (πv) = T i k v; reason: false as printed: n = m = 2, Tᵢ¹(v₋ᵢ) = vⱼ¹g(vⱼ²), Tᵢ²(v₋ᵢ) = vⱼ²g(vⱼ¹), g(t) = 1 + t/(1+t), ties unsold, is regular, SP, AS, continuous and AN, yet with i = j = 1, k = 1, v = [[1.6,1],[1,1]], ṽ = [[1.6,1],[1,3]] the column-1 entries of the others agree and the thresholds are 1.5 ≠ 1.75
--   - generalization: μ ∈ Γ̄_{M,N} (continuous, Definition 4) → μ in Γ_{M,N}: IsMechanism, IsRegular, SP, AS; no continuity hypothesis; reason: Γ̄ ⊆ Γ, so the statement specializes to the paper's under any reading of Definition 4; the result holds without continuity
--   - encoding: Tᵢᵏ : Πⱼ≠ᵢVⱼ → ℝ₊₊, the thresholds of Theorem 2 → any T : Fin n → Fin m → profile → ℝ with IsThresholdRep μ T (ignores row i, positive at positive profiles); reason: a function of v₋ᵢ is a function of the profile that ignores row i; the paper's T is such a representation
--   - reading: 𝒟: elements of each column sum up to 1 (p.5) → IsFeasible: each column sums to at most 1; reason: p.7 sets 𝒟 = {0,1}ᵐ for one buyer, Theorem 4 assumes selling all objects as a separate hypothesis and §7.2 uses a mechanism that sells nothing; with sums = 1 every mechanism would sell everything. Under the sells-all hypothesis the two readings coincide
--   - generalization: m ≥ 2 and n ≥ 1 (§3, p.5: "Fix any m ≥ 2 and n ≥ 1") → any n, m : ℕ; reason: covers the paper's range; the argument (utility identity plus AN) does not use m ≥ 2
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), Proposition 2, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_StrategyproofMultidim_IsMechanism
import Definitions.Def_StrategyproofMultidim_IsRegular
import Definitions.Def_StrategyproofMultidim_SP
import Definitions.Def_StrategyproofMultidim_AS
import Definitions.Def_StrategyproofMultidim_AN
import Definitions.Def_StrategyproofMultidim_IsThresholdRep

namespace StrategyproofMultidim

/-- **Proposition 2 (corrected): thresholds are anonymous** (p.22).
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.22: "Proposition 2. If a mechanism μ ∈ Γ̄_{M,N} satisfies AN, then for any i, j ∈ N,
any k ∈ M, and any v, ṽ ∈ 𝒱, vᵏ₋ᵢ = ṽᵏ₋ⱼ ⟹ Tᵢᵏ(v₋ᵢ) = Tⱼᵏ(ṽ₋ⱼ)."

For a mechanism in `Γ_{M,N}` satisfying AN, with threshold representation `T`, relabelling the
buyers by any permutation `π` carries buyer `i`'s thresholds to buyer `π i`'s: the threshold of
buyer `π i` for object `k` at the relabelled profile `πv` equals that of buyer `i` at `v`.
Equivalently: if the other buyers' rows `ṽ₋ⱼ` are a relabelling of `v₋ᵢ`, then
`Tᵢᵏ(v₋ᵢ) = Tⱼᵏ(ṽ₋ⱼ)`.

**Formalization Note.** As printed (only column `k` of the others agreeing) the statement is
false: a counterexample in `Γ̄` with AN is `n = m = 2`, `Tᵢ¹(v₋ᵢ) = vⱼ¹ g(vⱼ²)`,
`Tᵢ² = vⱼ² g(vⱼ¹)`, `g(t) = 1 + t/(1+t)`, at `v = [[1.6,1],[1,1]]`, `ṽ = [[1.6,1],[1,3]]`, `i = j = 1`
(thresholds `1.5 ≠ 1.75`). The hypothesis is corrected to whole rows. `πv = fun t => v (π.symm t)`.
Continuity is not assumed. -/
theorem proposition_2 {n m : ℕ} (μ : Mechanism n m) (hM : IsMechanism μ) (hR : IsRegular μ) (hSP : SP μ) (hAS : AS μ) (hAN : AN μ)
    (T : Fin n → Fin m → (Fin n → Fin m → ℝ) → ℝ) (hT : IsThresholdRep μ T)
    (π : Equiv.Perm (Fin n)) (v : Fin n → Fin m → ℝ) (hv : PosProfile v) (i : Fin n) (k : Fin m) :
    T (π i) k (fun t => v (π.symm t)) = T i k v := by sorry

end StrategyproofMultidim
