-- Prove2me | Theorems.Thm_PLIAG_proposition_3_1
-- name    : PLIAG.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:29:39.527332+00:00
-- url     : https://prove2.me/theorems/3774bb53-f5cd-4d8a-adf6-daa35881a3ee
-- title:
--   Proposition 3.1 — the subproblem (3.1) has a unique solution, in $\operatorname{int}\operatorname{dom}w$ (corrected: needs $\operatorname{dom}h\cap\operatorname{int}\operatorname{dom}w\neq\emptyset$)
-- statement:
--   Throughout, $w$ is a Legendre function with constraint set $\mathcal Q=\overline{\operatorname{dom}w}$, $h$ is proper, lower semicontinuous and convex, the optimal solution set $\mathcal X$ of (1.1) is nonempty and compact, every block $\mathcal J_k$ is nonempty and every delay satisfies $\tau_k^n\le\tau$ (assumption A0).
--
--   Assume B1, and B4 if $\tau>0$; assume moreover $\operatorname{dom}h\cap\operatorname{int}\operatorname{dom}w\neq\emptyset$. Let the step size satisfy $0<\alpha_k\le 1/\sum_{j\in\mathcal J_k}L_j$ when $\tau=0$ and $0<\alpha_k\le 1/\big(\ell(2)\sum_{j\in\mathcal J_k}L_j\big)$ when $\tau>0$. If $x_j\in\operatorname{int}\operatorname{dom}w$ for all $j\le k$, then the subproblem
--
--   $$
--   \min_{x\in\mathcal Q}\ \Phi_k(x)
--   $$
--
--   of (3.1) has a unique optimal solution, and that solution belongs to $\operatorname{int}\operatorname{dom}w$.
--
--   The proposition makes the PLIAG method well defined: by induction, every iterate exists, is unique, and stays in the interior of $\operatorname{dom}w$, where the gradients and Bregman distances of the next step are defined.
--
--   Differences from the source:
--   - correction: assumptions B1 and B4 only → adds dom h ∩ int dom w ≠ ∅ (the first clause of B2); reason: the printed statement is false: d = N = 1, τ = 0, w(x) = x log x − x on [0, ∞), f_1 ≡ 0, L_1 = 1, h = δ_{0}, α = 1, x_0 = 1 satisfy every printed hypothesis (and X = {0} is nonempty compact), but the unique solution of (3.1) is 0 ∉ int dom w
--   - encoding: step size α_k of iteration k → a real α > 0 used in Φ_k; reason: only the k-th step enters the k-th subproblem
--   - encoding: problem (3.1) has a unique optimal solution which belongs to int dom w → there is a unique minimizer of Φ_k over Q, and every minimizer lies in int dom w; reason: same content
--   - generalization: τ the smallest upper bound for all delayed indexes (A0), B4 required when it is positive → τ any natural number with τ_k^n ≤ τ for all k, n; the B4 inequality required when τ > 0; reason: the smallest bound is an instance, for which the hypotheses are exactly the paper’s; the proof only uses τ_k^n ≤ τ
--   - encoding: ℓ monotonically increasing with ℓ(1) = 1 (introduced by B4 when τ > 0; ℓ(τ+1) = ℓ(1) = 1 when τ = 0) → ℓ : ℕ → ℝ with Monotone ℓ and ℓ 1 = 1 always; reason: when τ = 0 only ℓ(1) = 1 enters; ℓ(0) is never read and a monotone ℓ on the positive integers extends by ℓ(0) := ℓ(1)
--   - reading: ∅ ≠ J_k ⊆ J_k (p.8) → J k : Finset (Fin N) with (J k).Nonempty, I_k = (J k)ᶜ; reason: misprint for J_k ⊆ N = {1, …, N}; components indexed by Fin N
--   - encoding: x_k = x_0 for k < 0; Σ_{j=k−τ}^k with negative j → truncated ℕ subtraction k − τ_k^j and Finset.Icc (k − τ) k; reason: same iterates; the omitted negative-index terms are D_w(x_0, x_0) = 0
--   - encoding: functions ℝ^d → (−∞, ∞], convex in the extended sense → EuclideanSpace ℝ (Fin d) → EReal, convexity as convexity of the epigraph; reason: Lean convention; same instances
--   - encoding: D_w(y, x) defined for y ∈ dom w, x ∈ int dom w → bregman w y x in EReal, equal to +∞ for y ∉ dom w; reason: the paper extended arithmetic; identical on dom w, and it makes inf over X and (3.1) mean what the page says
--   - encoding: ∇w, ∇f_j on int dom w → gradient of the real functions (w ·).toReal, (f_j ·).toReal; reason: w and f_j are finite on the open set int dom w, so the gradients coincide
--   - encoding: B4 for every finite sequence {v_1, …, v_k} in int dom w → B4 for every v : ℕ → ℝ^d with all terms in int dom w; reason: equivalent: a finite sequence extends by repeating its last term, and each inequality reads only v_j, …, v_k
-- source:
--   Zhang, Dai, Guo, Peng, Proximal-Like Incremental Aggregated Gradient Method with Linear Convergence under Bregman Distance Growth Conditions, arXiv:1711.01136v3, Proposition 3.1, p.8 (proof pp.22)

import Mathlib
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PLIAG_IsLegendre
import Definitions.Def_PLIAG_optSet
import Definitions.Def_PLIAG_AssumptionB1
import Definitions.Def_PLIAG_AssumptionB4
import Definitions.Def_PLIAG_Phik

namespace PLIAG

/-- **Proposition 3.1, corrected** (Zhang–Dai–Guo–Peng, arXiv:1711.01136v3, p.8). Assume B1 and
B4. Let `α_k ≤ 1/Σ_{j ∈ J_k} L_j` when `τ = 0` and `α_k ≤ 1/(ℓ(2) Σ_{j ∈ J_k} L_j)` when
`τ > 0`. If `x_j ∈ int dom w` for all `j ≤ k`, then problem (3.1) has a unique optimal solution,
which belongs to `int dom w`.

**Correction.** The printed proposition omits `dom h ∩ int dom w ≠ ∅` (the first clause of B2),
and is false without it: `d = N = 1`, `τ = 0`, `w(x) = x log x − x` on `[0, ∞)`, `f_1 ≡ 0`,
`L_1 = 1`, `h = δ_{0}`, `α = 1`, `x_0 = 1` satisfy every printed hypothesis (and `X = {0}` is
nonempty compact), but the unique solution of (3.1) is `0 ∉ int dom w`. The hypothesis `hdom` is
added.

**Formalization Note.** The step at iteration `k` is `α > 0`; only the `k`-th subproblem is
concerned. Standing assumptions are kept: `h` proper lsc convex (p.2), `w` Legendre, `X` nonempty
compact (p.5), `J_k ≠ ∅` and delays `≤ τ` (step (ii), A0). B4 is required only when `τ > 0`. -/
theorem proposition_3_1 {d N : ℕ} (w : EuclideanSpace ℝ (Fin d) → EReal)
    (f : Fin N → EuclideanSpace ℝ (Fin d) → EReal) (h : EuclideanSpace ℝ (Fin d) → EReal)
    (Lc : Fin N → ℝ) (ℓ : ℕ → ℝ) (τ : ℕ) (J : ℕ → Finset (Fin N)) (τd : ℕ → Fin N → ℕ)
    (α : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin d))
    (k : ℕ)
    (hw : IsLegendre w) (hh : TensorAHPE.IsProperClosedConvex h)
    (hXne : (optSet w f h).Nonempty) (hXc : IsCompact (optSet w f h))
    (hJ : ∀ k, (J k).Nonempty) (hA0 : ∀ k n, τd k n ≤ τ)
    (hB1 : AssumptionB1 w f Lc)
    (hℓm : Monotone ℓ) (hℓ1 : ℓ 1 = 1) (hB4 : 0 < τ → AssumptionB4 w ℓ)
    (hdom : (AubinLipschitz.effDom h ∩ interior (AubinLipschitz.effDom w)).Nonempty)
    (hα : 0 < α) (hα0 : τ = 0 → α ≤ 1 / ∑ j ∈ J k, Lc j)
    (hαpos : 0 < τ → α ≤ 1 / (ℓ 2 * ∑ j ∈ J k, Lc j))
    (hx : ∀ j ≤ k, x j ∈ interior (AubinLipschitz.effDom w)) :
    (∃! z, z ∈ closure (AubinLipschitz.effDom w) ∧
        ∀ y ∈ closure (AubinLipschitz.effDom w), Phik w f h J τd α x k z ≤ Phik w f h J τd α x k y) ∧
    ∀ z, z ∈ closure (AubinLipschitz.effDom w) →
        (∀ y ∈ closure (AubinLipschitz.effDom w), Phik w f h J τd α x k z ≤ Phik w f h J τd α x k y) →
        z ∈ interior (AubinLipschitz.effDom w) := by sorry

end PLIAG
