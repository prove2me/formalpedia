-- Prove2me | Theorems.Thm_SubmodSparsify_claim_4_5
-- name    : SubmodSparsify.claim_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:25.528199+00:00
-- url     : https://prove2.me/theorems/3f5fa426-8ca8-4610-bbc1-7729a7c826d6
-- title:
--   Claim 4.5 — residual bound (P1): $\Delta_i(S, U_\theta) \le \theta p_i$
-- statement:
--   Let $f_1, \dots, f_m : 2^{[n]} \to \mathbb R_{\ge 0}$ be submodular with $f_i(\emptyset) = f_i([n]) = 0$, with Algorithm 1's shares $s_i^{(u)}$, $t_i^{(v)}$, weights $p_i$ and influences $\inf_S$. For any query $S \subseteq [n]$ and threshold $\theta \ge 0$, let $U_\theta := \{w \in [n] : \inf_S(w) \le \theta\}$. Then for every $u \in S$, $v \in \bar S$ and $i \in [m]$,
--
--   $$f_i^{\to}(u, U_\theta \setminus S) \le \theta\, s_i^{(u)}, \qquad f_i^{\to}(U_\theta \cap S, v) \le \theta\, t_i^{(v)},$$
--
--   and consequently
--
--   $$\Delta_i(S, U_\theta) \le \theta \cdot p_i .$$
--
--   Leaving the low-influence coordinates free costs each component at most $\theta$ times its sampling weight; this is property (P1) of the chaining framework.
--
--   Differences from the source:
--   - encoding: ground set [n] = {1, …, n}, subsets of [n], components f_1, …, f_m → Fin n (paper index = value + 1), Finset (Fin n), f : Fin m → Finset (Fin n) → ℝ; reason: Lean representation; same instances
--   - encoding: standing assumption of §4 (p.18): every component normalized, f_i(∅) = f_i([n]) = 0, nonnegative submodular → explicit hypotheses hf0, hsub, hempty, huniv; reason: the section's standing hypotheses written as binders; same instances
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6…), Claim 4.5, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SubmodSparsify_weights

namespace SubmodSparsify

/-- **Claim 4.5** (p.24): the residual bound (P1).

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), Claim 4.5, p.24.

For any query `S ⊆ [n]` and threshold `θ ≥ 0`, let `U_θ := {w ∈ [n] : inf_S(w) ≤ θ}`. Then for
every `u ∈ S`, `v ∈ S̄` and `i ∈ [m]`, `f→ᵢ(u, U_θ \ S) ≤ θ s_i^{(u)}` and
`f→ᵢ(U_θ ∩ S, v) ≤ θ t_i^{(v)}`, and consequently `Δᵢ(S, U_θ) ≤ θ pᵢ`.

**Formalization Note.** `[n]` is `Fin n`, components `f : Fin m → Finset (Fin n) → ℝ`
(paper indices = values + 1), `S̄ = Sᶜ`. The hypotheses on `f` are those of Theorem 4.1, the
standing assumption of §4 (p.18): nonnegative, submodular, `fᵢ(∅) = fᵢ([n]) = 0`. `inShare f u i`
is `s_i^{(u)}`, `outShare f v i` is `t_i^{(v)}`, `weights f i` is `pᵢ`, `influence f S w` is
`inf_S(w)` of (25), `residual f i S U` is `Δᵢ(S, U)` of (24) (module `SubmodSparsify.weights`). -/
theorem claim_4_5 {n m : ℕ} (f : Fin m → Finset (Fin n) → ℝ) (hf0 : ∀ i S, 0 ≤ f i S)
    (hsub : ∀ i, NonmonotoneSubmod.Shared.Submodular (f i))
    (hempty : ∀ i, f i ∅ = 0) (huniv : ∀ i, f i Finset.univ = 0)
    (S : Finset (Fin n)) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∀ u ∈ S, ∀ i : Fin m,
      blockMinCut (f i) {u} (Finset.univ.filter (fun w => influence f S w ≤ θ) \ S) ≤
        θ * inShare f u i) ∧
    (∀ v ∈ Sᶜ, ∀ i : Fin m,
      blockMinCut (f i) (Finset.univ.filter (fun w => influence f S w ≤ θ) ∩ S) {v} ≤
        θ * outShare f v i) ∧
    (∀ i : Fin m,
      residual f i S (Finset.univ.filter (fun w => influence f S w ≤ θ)) ≤
        θ * weights f i) := by sorry

end SubmodSparsify
