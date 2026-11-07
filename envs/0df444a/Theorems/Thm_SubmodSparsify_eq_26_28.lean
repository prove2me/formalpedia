-- Prove2me | Theorems.Thm_SubmodSparsify_eq_26_28
-- name    : SubmodSparsify.eq_26_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:32.349005+00:00
-- url     : https://prove2.me/theorems/a9b553a5-2a53-4ea8-b6d0-7b724f600863
-- title:
--   §4.3, Steps 1–2, (26)–(28) — positive chaining: $\sum_j \ell_j \max_i z_{i,j}/p_i \le 8F(S)$
-- statement:
--   Let $f_1, \dots, f_m : 2^{[n]} \to \mathbb R_{\ge 0}$ be submodular with $f_i(\emptyset) = f_i([n]) = 0$, $F := \sum_i f_i$, with Algorithm 1's weights $p_i$ and the influences $\inf_S$. Fix a query $S$ with $F(S) > 0$. For $j \ge 0$ let
--
--   $$\theta_j := 2^{-j} F(S), \quad U_j := \{w : \inf_S(w) \le \theta_j\}, \quad I_j := S \setminus U_j, \quad O_j := \bar S \setminus U_j, \quad \ell_j := |I_j| + |O_j|,$$
--
--   let $J \ge 1$ be such that $\theta_J$ is strictly smaller than every positive value among $\{\inf_S(w)\}$, and for $1 \le j \le J$ let $z_{i,j} := f_i^{\to}(I_j, O_j) - f_i^{\to}(I_{j-1}, O_{j-1})$. Then for every $i$ and $1 \le j \le J$,
--
--   $$\sum_{j=1}^J z_{i,j} = f_i(S), \qquad 0 \le z_{i,j} \le \Delta_i(S, U_{j-1}) \le \theta_{j-1} p_i, \qquad (26)$$
--
--   $$\sum_{j=1}^J \ell_j \theta_{j-1} \le 4 \sum_{w \in [n]} \inf_S(w) \le 8 F(S), \qquad (27)$$
--
--   $$\sum_{j=1}^J \ell_j \max_{i \in [m]} \frac{z_{i,j}}{p_i} \le 8 F(S). \qquad (28)$$
--
--   The value $f_i(S)$ is thus written as a telescoping sum of nonnegative increments whose total description-weighted scale is controlled by $F(S)$.
--
--   Differences from the source:
--   - encoding: ground set [n] = {1, …, n}, subsets of [n], components f_1, …, f_m → Fin n (paper index = value + 1), Finset (Fin n), f : Fin m → Finset (Fin n) → ℝ; reason: Lean representation; same instances
--   - encoding: standing assumption of §4 (p.18): every component normalized, f_i(∅) = f_i([n]) = 0, nonnegative submodular → explicit hypotheses hf0, hsub, hempty, huniv; reason: the section's standing hypotheses written as binders; same instances
--   - encoding: z_{i,j}/p_i with the convention 0/0 := 0 (p.10) → Lean division (x/0 = 0); reason: the components with p_i = 0 vanish identically (p.26), so z_{i,j} = 0 there and both conventions give 0
--   - encoding: "Let J ≥ 1 be large enough that …" → the statement holds for every J ≥ 1 with that property; reason: the paper's J is any such J
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6…), proof of Theorem 4.1, §4.3, Step 1, display (26), p.26 (PDF p.28); Step 2, displays (27)–(28), p.27 (PDF p.29)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SubmodSparsify_weights

namespace SubmodSparsify

/-- **§4.3, Steps 1–2, displays (26), (27), (28)** (pp.26–27): positive chaining.

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), proof of Theorem 4.1, §4.3, Step 1 (display (26), p.26) and Step 2 (displays (27)–(28),
p.27).

Fix a query `S` with `F(S) > 0`. For `j ≥ 0` let `θ_j := 2^{−j}F(S)`,
`U_j := {w : inf_S(w) ≤ θ_j}`, `I_j := S \ U_j`, `O_j := S̄ \ U_j`, `ℓ_j := |I_j| + |O_j|`, and
for `1 ≤ j ≤ J`, `z_{i,j} := f→ᵢ(I_j, O_j) − f→ᵢ(I_{j−1}, O_{j−1})`, where `J ≥ 1` is such that
`θ_J` is strictly smaller than every positive value among `{inf_S(w)}`. Then
(26) `Σ_{j=1}^J z_{i,j} = fᵢ(S)` and `0 ≤ z_{i,j} ≤ Δᵢ(S, U_{j−1}) ≤ θ_{j−1} pᵢ`;
(27) `Σ_{j=1}^J ℓ_j θ_{j−1} ≤ 4 Σ_w inf_S(w) ≤ 8F(S)`;
(28) `Σ_{j=1}^J ℓ_j max_{i∈[m]} z_{i,j}/pᵢ ≤ 8F(S)`.

**Formalization Note.** `[n]` is `Fin n`, components `f : Fin m → Finset (Fin n) → ℝ`
(paper indices = values + 1), `S̄ = Sᶜ`. The hypotheses on `f` are those of Theorem 4.1, the
standing assumption of §4 (p.18): nonnegative, submodular, `fᵢ(∅) = fᵢ([n]) = 0`. `inShare f u i`
is `s_i^{(u)}`, `outShare f v i` is `t_i^{(v)}`, `weights f i` is `pᵢ`, `influence f S w` is
`inf_S(w)` of (25), `residual f i S U` is `Δᵢ(S, U)` of (24) (module `SubmodSparsify.weights`). `zᵢⱼ/pᵢ` is Lean's division (`x/0 = 0`), the paper's convention `0/0 := 0` (p.10) on the
components with `pᵢ = 0` (which vanish identically, p.26). The maximum over `i` is `⨆ i`
(`m ≥ 1` here since `F(S) > 0`). -/
theorem eq_26_28 {n m : ℕ} (f : Fin m → Finset (Fin n) → ℝ) (hf0 : ∀ i S, 0 ≤ f i S)
    (hsub : ∀ i, NonmonotoneSubmod.Shared.Submodular (f i))
    (hempty : ∀ i, f i ∅ = 0) (huniv : ∀ i, f i Finset.univ = 0)
    (S : Finset (Fin n)) (hS : 0 < ∑ i, f i S) (J : ℕ) (hJ : 1 ≤ J)
    (hJsmall : ∀ w, 0 < influence f S w → (∑ i, f i S) / 2 ^ J < influence f S w) :
    let F : ℝ := ∑ i, f i S
    let U : ℕ → Finset (Fin n) := fun j => Finset.univ.filter (fun w => influence f S w ≤ F / 2 ^ j)
    let I : ℕ → Finset (Fin n) := fun j => S \ U j
    let O : ℕ → Finset (Fin n) := fun j => Sᶜ \ U j
    let ℓ : ℕ → ℝ := fun j => ((I j).card + (O j).card : ℕ)
    let z : Fin m → ℕ → ℝ := fun i j =>
      blockMinCut (f i) (I j) (O j) - blockMinCut (f i) (I (j - 1)) (O (j - 1))
    (∀ i, ∑ j ∈ Finset.Icc 1 J, z i j = f i S) ∧
    (∀ i, ∀ j ∈ Finset.Icc 1 J, 0 ≤ z i j ∧ z i j ≤ residual f i S (U (j - 1)) ∧
      residual f i S (U (j - 1)) ≤ F / 2 ^ (j - 1) * weights f i) ∧
    (∑ j ∈ Finset.Icc 1 J, ℓ j * (F / 2 ^ (j - 1)) ≤ 4 * ∑ w, influence f S w ∧
      4 * ∑ w, influence f S w ≤ 8 * F) ∧
    ∑ j ∈ Finset.Icc 1 J, ℓ j * (⨆ i, z i j / weights f i) ≤ 8 * F := by sorry

end SubmodSparsify
