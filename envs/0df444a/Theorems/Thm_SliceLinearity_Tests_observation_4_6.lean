-- Prove2me | Theorems.Thm_SliceLinearity_Tests_observation_4_6
-- name    : SliceLinearity.Tests.observation_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:37:57.779102+00:00
-- url     : https://prove2.me/theorems/6f84557c-4a12-4c1b-8053-227c20f41f73
-- title:
--   Observation 4.6 — replacing one argument of a multilinear form at a time
-- statement:
--   Let $T$ be linear or conjugate-linear in each of its $k$ arguments, and let $\|\cdot\|$ be a norm. Fix inputs $f_1,\dots,f_k$ and $g_1,\dots,g_k$. Suppose that, for every $i\in[k]$, every $h$, and every choice $u_j\in\{f_j,g_j\}$ ($j\ne i$),
--   $$|T(u_1,\dots,u_{i-1},h,u_{i+1},\dots,u_k)|\le C\,\|h\|.$$
--   Then
--   $$|T(f_1,\dots,f_k)-T(g_1,\dots,g_k)|\le C\sum_{i=1}^k\|f_i-g_i\|\le kC\max_i\|f_i-g_i\|.$$
--   In particular, for $T=\Lambda_{k,\lambda}$ ($k\ge3$, $\lambda\ne0$) and inputs bounded by one, the hypothesis holds with $C=1$ and the uniform $L^1(H)$ norm.
--
--   The second part is stated as the second conjunct: for every finite field $\mathbb F$, every finite $\mathbb F$-vector space $H$, and all $|f_j|,|g_j|\le1$, $|\Lambda_{k,\lambda}(u_1,\dots,h,\dots,u_k)|\le\mathbb E_{x\sim H}|h(x)|$.
--
--   Differences from the source:
--   - generalization: T linear or conjugate-linear in each argument → T additive in each argument (T(…, a + b, …) = T(…, a, …) + T(…, b, …)); reason: linear and conjugate-linear maps are additive, so every T of the source is covered
--   - generalization: ‖·‖ a norm → N : E → ℝ any nonnegative function; reason: every norm is nonnegative, so every norm of the source is covered
--   - encoding: max_i ‖fᵢ − gᵢ‖ → ⨆ i, N (f i − g i) over Fin k; reason: a finite supremum equals the maximum for k ≥ 1; for k = 0 both sides are 0
--   - encoding: Λ_{k,λ} on H = span(Supp ν) ⊆ F_qⁿ with the L¹(H) norm → mixedAvg on an arbitrary finite F-vector space H with l1Unif h = E_{x∼H}|h(x)|; reason: every span of a support is a finite vector space and conversely up to isomorphism; same instances
-- source:
--   Aydin, Larsen, Mittal, Richelson, Roy, Low Soundness Linearity Testing on Subsets of the Hypercube, STOC 2027 submission (manuscript sha256 457be236…), §4.1, p. 23 (PDF 25), Observation 4.6

import Mathlib
import Definitions.Def_SliceLinearity_Tests_FiniteFourier

set_option autoImplicit false

namespace SliceLinearity.Tests

/-- **Observation 4.6** (Replacing one function at a time), p. 23 (PDF 25).

(1) Let `T` be additive (in particular linear or conjugate-linear) in each of its `k` arguments and
`N` a norm (here: any nonnegative function). Fix `f₁, …, f_k`, `g₁, …, g_k`. If for every `i`, every
`h` and every choice `u_j ∈ {f_j, g_j}` (`j ≠ i`), `|T(u₁, …, u_{i−1}, h, u_{i+1}, …, u_k)| ≤ C · N(h)`,
then `|T(f) − T(g)| ≤ C ∑ᵢ N(fᵢ − gᵢ) ≤ kC · maxᵢ N(fᵢ − gᵢ)`.

(2) In particular, for `T = Λ_{k,λ}` (`k ≥ 3`, `λ ≠ 0`) and inputs bounded by one, the hypothesis holds
with `C = 1` and the uniform `L¹(H)` norm. -/
theorem observation_4_6 :
    (∀ {E : Type*} [AddCommGroup E] {k : ℕ} (T : (Fin k → E) → ℂ) (N : E → ℝ),
      (∀ x, 0 ≤ N x) →
      (∀ (i : Fin k) (u : Fin k → E) (a b : E),
        T (Function.update u i (a + b)) = T (Function.update u i a) + T (Function.update u i b)) →
      ∀ (C : ℝ) (f g : Fin k → E),
        (∀ (i : Fin k) (h : E) (u : Fin k → E), (∀ j, j ≠ i → u j = f j ∨ u j = g j) →
          ‖T (Function.update u i h)‖ ≤ C * N h) →
        ‖T f - T g‖ ≤ C * ∑ i, N (f i - g i) ∧
          C * ∑ i, N (f i - g i) ≤ (k : ℝ) * C * ⨆ i, N (f i - g i)) ∧
    (∀ {F H : Type*} [Field F] [Fintype F] [AddCommGroup H] [Module F H] [Fintype H]
      (k : ℕ), 3 ≤ k → ∀ lam : F, lam ≠ 0 →
      ∀ f g : Fin k → H → ℂ, (∀ i x, ‖f i x‖ ≤ 1) → (∀ i x, ‖g i x‖ ≤ 1) →
      ∀ (i : Fin k) (h : H → ℂ) (u : Fin k → H → ℂ), (∀ j, j ≠ i → u j = f j ∨ u j = g j) →
        ‖mixedAvg k lam (Function.update u i h)‖ ≤ 1 * l1Unif h) := by sorry

end SliceLinearity.Tests
