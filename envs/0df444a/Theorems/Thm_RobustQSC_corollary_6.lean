-- Prove2me | Theorems.Thm_RobustQSC_corollary_6
-- name    : RobustQSC.corollary_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:53:16.05573+00:00
-- url     : https://prove2.me/theorems/db5b69fd-1aa6-4752-8106-b292f481c3f3
-- title:
--   Corollary 6, p.53 — compatible flat net for the centered $A$-supported class
-- statement:
--   Fix $T\ge12$, $\kappa>0$ and $0<\varepsilon\le1$. For a sufficiently large universal constant $C>0$, the following holds with probability $1-2^{-\Omega(n)}$ over $\mu\sim\boldsymbol\mu$, for all sufficiently large $n$. Let
--
--   $$
--   Q_{\kappa,A}=\bigl\{q:\mathrm{supp}(q)\subseteq A,\ \mathbb E_\mu q=0,\ \|q\|_{L^2(\mu)}=1,\ \mathrm{Inf}^{\mathrm{int}(A)}_\mu(q)\le\kappa n\bigr\}
--   $$
--
--   and suppose $0<\gamma\le1/3$ and $H(\gamma)<1/3$ for $\gamma=CT^5\kappa/\varepsilon^2$, with $H$ the binary entropy. Then there is a finite family $Q^{(\varepsilon)}_{\kappa,A}$ such that:
--
--   1. every $q\in Q_{\kappa,A}$ has some $v\in Q^{(\varepsilon)}_{\kappa,A}$ with $\|q-v\|_{L^2(\mu)}\le\varepsilon$;
--   2. every $v\in Q^{(\varepsilon)}_{\kappa,A}$ is $\mu$-compatible and satisfies $\max_x\mu(x)|v(x)|^2\le\|\mu\|_\infty^{1/3}$;
--   3. $\log|Q^{(\varepsilon)}_{\kappa,A}|\le N^{H(\gamma)+o(1)}\log(C/\varepsilon)$.
--
--   This net is what Theorem 5 is union-bounded over.
--
--   Differences from the source:
--   - reading: "for a sufficiently large universal constant $C$" → one constant $C>0$ chosen before $T,\kappa,\varepsilon$; the constant of $\Omega(n)$, the $o(1)$ sequence and $n_0$ may depend on $T,\kappa,\varepsilon$; reason: equal strength: a larger $C$ only shrinks the admissible parameters and enlarges the bound on $\gamma\le1/3$, where $H$ is increasing
--   - encoding: $H$ → `binEntropy2`, in bits; reason: the exponent of $N=2^n$ in the dimension count on p.53 requires base $2$
--   - encoding: $\mathbb E_\mu q=0$, $\|q\|_{L^2(\mu)}=1$ → `Compatible μ q`; reason: same two equations
--   - encoding: "with probability $1-2^{-\Omega(n)}$", "for $n$ large" → a constant $c_0>0$ and a threshold $n_0$ with the outer measure of the failure event at most $2^{-c_0n}$ for $n\ge n_0$; reason: the standard meaning; the failure event is bounded in outer measure, so no measurability is assumed
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), Corollary 6, p.53; A(T), p.47; interior influence, p.48

import Definitions.Def_RobustQSC_dirichletOne
import Definitions.Def_RobustQSC_LocalEscape
import Definitions.Def_RobustQSC_infMu
import Definitions.Def_RobustQSC_Compatible
import Definitions.Def_QAlgorithms_Defs_Information

namespace RobustQSC

open QAlgorithms MeasureTheory Filter Topology

/-- **Corollary 6 (Compatible flat net for the centered `A`-supported class).** Fix `T ≥ 12`,
`κ > 0` and `0 < ε ≤ 1`. For a sufficiently large universal constant `C > 0` the following holds
with probability `1 − 2^{−Ω(n)}` over `μ ∼ 𝛍`, for all sufficiently large `n`. Let
`Q_{κ,A} = {q : supp(q) ⊆ A, E_μ q = 0, ‖q‖_{L²(μ)} = 1, Inf^{int(A)}_μ(q) ≤ κn}`. Suppose
`0 < γ ≤ 1/3` and `H(γ) < 1/3` for `γ = C T⁵κ/ε²`. Then there is a finite family
`Q^{(ε)}_{κ,A}` such that every `q ∈ Q_{κ,A}` is within `ε` in `L²(μ)` of some member, every
member `v` is `μ`-compatible with `max_x μ(x)|v(x)|² ≤ ‖μ‖_∞^{1/3}`, and
`log|Q^{(ε)}_{κ,A}| ≤ N^{H(γ)+o(1)} log(C/ε)`.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles for
total influence*, arXiv:2607.27184 (sha256 09d2692e…), Corollary 6, p.53; `A = A(T)`, p.47; `Inf^{int(A)}_µ`, p.48.

**Formalization Note.**
1. `C` is chosen before `T, κ, ε`; the constant of `Ω(n)`, the `o(1)` sequence `e` and `n₀` may
   depend on `T, κ, ε`.
2. `H` is the binary entropy in bits (`binEntropy2`); `A = goodSet T μ`; `‖·‖_{L²(μ)}` is
   `l2Norm μ`; `‖μ‖_∞ = ⨆_x μ(x)`; `E_μ q = 0` and `‖q‖_{L²(μ)} = 1` are `Compatible μ q`.
3. The family is a `Finset` of functions; the bad event is "no such family exists". -/
theorem corollary_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 12 ≤ T → ∀ κ : ℝ, 0 < κ → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      0 < C * T ^ 5 * κ / ε ^ 2 → C * T ^ 5 * κ / ε ^ 2 ≤ 1 / 3 →
      binEntropy2 (C * T ^ 5 * κ / ε ^ 2) < 1 / 3 →
      ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
        dirichletOne (Qubits n) {μ | ¬ ∃ Q : Finset (Qubits n → ℂ),
            (∀ q : Qubits n → ℂ, (∀ x, x ∉ goodSet T μ → q x = 0) → Compatible μ q →
              infInt μ (goodSet T μ) q ≤ κ * n → ∃ v ∈ Q, l2Norm μ (q - v) ≤ ε) ∧
            (∀ v ∈ Q, Compatible μ v ∧ ∀ x, μ x * ‖v x‖ ^ 2 ≤ (⨆ y, μ y) ^ (1 / 3 : ℝ)) ∧
            Real.log Q.card ≤
              ((2 : ℝ) ^ n) ^ (binEntropy2 (C * T ^ 5 * κ / ε ^ 2) + e n) * Real.log (C / ε)}
          ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(c₀ * n))) := by sorry

end RobustQSC
