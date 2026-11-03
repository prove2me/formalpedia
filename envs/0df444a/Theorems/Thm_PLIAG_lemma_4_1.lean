-- Prove2me | Theorems.Thm_PLIAG_lemma_4_1
-- name    : PLIAG.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:29:21.078735+00:00
-- url     : https://prove2.me/theorems/5e14cd1c-3128-4783-8a53-dbca4dfb032f
-- title:
--   Lemma 4.1 — descent lemma with delayed terms
-- statement:
--   Throughout, $w$ is a Legendre function with constraint set $\mathcal Q=\overline{\operatorname{dom}w}$, $h$ is proper, lower semicontinuous and convex, the optimal solution set $\mathcal X$ of (1.1) is nonempty and compact, every block $\mathcal J_k$ is nonempty and every delay satisfies $\tau_k^n\le\tau$ (assumption A0).
--
--   Assume B1, B2, and B4 if $\tau>0$; let $\ell$ be monotonically increasing with $\ell(1)=1$, and let the step size be a constant $\alpha>0$. Let $x_j\in\operatorname{int}\operatorname{dom}w$ for all $j\le k$, and let $x_{k+1}$ be obtained via (3.1), i.e. $x_{k+1}$ minimizes $\Phi_k$ over $\mathcal Q$. With $L=\max_{k\ge0}\sum_{j\in\mathcal J_k}L_j$ and
--
--   $$
--   \Delta_k:=L\cdot\ell(\tau+1)\sum_{j=k-\tau}^{k}D_w(x_{j+1},x_j),
--   $$
--
--   for every $x\in\operatorname{dom}w$,
--
--   $$
--   \Phi(x_{k+1})\ \le\ \Phi(x)+\frac1\alpha D_w(x,x_k)-\frac1\alpha D_w(x,x_{k+1})-\frac1\alpha D_w(x_{k+1},x_k)+\Delta_k .
--   $$
--
--   This generalizes the descent lemma of the proximal gradient method and of the NoLips method to delayed, incremental gradients; the delay costs the error term $\Delta_k$. Both Theorem 4.1 and Theorem 4.2 rest on it.
--
--   Differences from the source:
--   - generalization: τ the smallest upper bound for all delayed indexes (A0), B4 required when it is positive → τ any natural number with τ_k^n ≤ τ for all k, n; the B4 inequality required when τ > 0; reason: the smallest bound is an instance, for which the hypotheses are exactly the paper’s; the proof only uses τ_k^n ≤ τ
--   - encoding: ℓ monotonically increasing with ℓ(1) = 1 (introduced by B4 when τ > 0; ℓ(τ+1) = ℓ(1) = 1 when τ = 0) → ℓ : ℕ → ℝ with Monotone ℓ and ℓ 1 = 1 always; reason: when τ = 0 only ℓ(1) = 1 enters; ℓ(0) is never read and a monotone ℓ on the positive integers extends by ℓ(0) := ℓ(1)
--   - reading: ∅ ≠ J_k ⊆ J_k (p.8) → J k : Finset (Fin N) with (J k).Nonempty, I_k = (J k)ᶜ; reason: misprint for J_k ⊆ N = {1, …, N}; components indexed by Fin N
--   - encoding: x_k = x_0 for k < 0; Σ_{j=k−τ}^k with negative j → truncated ℕ subtraction k − τ_k^j and Finset.Icc (k − τ) k; reason: same iterates; the omitted negative-index terms are D_w(x_0, x_0) = 0
--   - encoding: L := max_{k≥0} Σ_{j∈J_k} L_j → Lmax Lc J := ⨆ k, Σ_{j ∈ J k} Lc j (real supremum); reason: the family takes finitely many values, so the supremum is the maximum
--   - encoding: x_{k+1} obtained via (3.1), x_{k+1} = arg min_{x∈Q} Φ_k(x) → hxk, hmin: x_{k+1} ∈ Q is a minimizer of Φ_k over Q = closure (edom w); reason: Φ_k is convex, every minimizer lies in int dom w (B2 and essential smoothness of w), where Φ_k is strictly convex, so the minimizer is the arg min
--   - encoding: functions ℝ^d → (−∞, ∞], convex in the extended sense → EuclideanSpace ℝ (Fin d) → EReal, convexity as convexity of the epigraph; reason: Lean convention; same instances
--   - encoding: D_w(y, x) defined for y ∈ dom w, x ∈ int dom w → bregman w y x in EReal, equal to +∞ for y ∉ dom w; reason: the paper extended arithmetic; identical on dom w, and it makes inf over X and (3.1) mean what the page says
--   - encoding: ∇w, ∇f_j on int dom w → gradient of the real functions (w ·).toReal, (f_j ·).toReal; reason: w and f_j are finite on the open set int dom w, so the gradients coincide
--   - encoding: B4 for every finite sequence {v_1, …, v_k} in int dom w → B4 for every v : ℕ → ℝ^d with all terms in int dom w; reason: equivalent: a finite sequence extends by repeating its last term, and each inequality reads only v_j, …, v_k
-- source:
--   Zhang, Dai, Guo, Peng, Proximal-Like Incremental Aggregated Gradient Method with Linear Convergence under Bregman Distance Growth Conditions, arXiv:1711.01136v3, Lemma 4.1, p.11 (proof pp.22–23)

import Mathlib
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PLIAG_IsLegendre
import Definitions.Def_PLIAG_bregman
import Definitions.Def_PLIAG_Phi
import Definitions.Def_PLIAG_optSet
import Definitions.Def_PLIAG_AssumptionB1
import Definitions.Def_PLIAG_AssumptionB2
import Definitions.Def_PLIAG_AssumptionB4
import Definitions.Def_PLIAG_Phik
import Definitions.Def_PLIAG_Delta

namespace PLIAG

/-- **Lemma 4.1 (Descent lemma with delayed terms)** (Zhang–Dai–Guo–Peng, arXiv:1711.01136v3,
p.11). Assume B1, B2 and B4. Let `x_j ∈ int dom w` for all `j ≤ k` and `x_{k+1}` be obtained via
(3.1). With `L := max_k Σ_{j ∈ J_k} L_j` and `Δ_k := L·ℓ(τ+1) Σ_{j=k−τ}^k D_w(x_{j+1}, x_j)`,
`Φ(x_{k+1}) ≤ Φ(x) + (1/α)D_w(x, x_k) − (1/α)D_w(x, x_{k+1}) − (1/α)D_w(x_{k+1}, x_k) + Δ_k`
for all `x ∈ dom w`.

**Formalization Note.** Constant step `α > 0` (§4 preamble). "Obtained via (3.1)" is: `x_{k+1}`
is a minimizer of `Φ_k` over `Q = cl dom w`. No step-size condition and no interiority of
`x_{k+1}` are assumed (neither is in the lemma). Standing assumptions are kept (`h` proper lsc
convex, `w` Legendre, `X` nonempty compact, `J_k ≠ ∅`, A0). B4 is required only when `τ > 0`.
Everything is in `EReal`. -/
theorem lemma_4_1 {d N : ℕ} (w : EuclideanSpace ℝ (Fin d) → EReal)
    (f : Fin N → EuclideanSpace ℝ (Fin d) → EReal) (h : EuclideanSpace ℝ (Fin d) → EReal)
    (Lc : Fin N → ℝ) (ℓ : ℕ → ℝ) (τ : ℕ) (J : ℕ → Finset (Fin N)) (τd : ℕ → Fin N → ℕ)
    (α : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin d))
    (k : ℕ)
    (hw : IsLegendre w) (hh : TensorAHPE.IsProperClosedConvex h)
    (hXne : (optSet w f h).Nonempty) (hXc : IsCompact (optSet w f h))
    (hJ : ∀ k, (J k).Nonempty) (hA0 : ∀ k n, τd k n ≤ τ)
    (hB1 : AssumptionB1 w f Lc) (hB2 : AssumptionB2 w h)
    (hℓm : Monotone ℓ) (hℓ1 : ℓ 1 = 1) (hB4 : 0 < τ → AssumptionB4 w ℓ)
    (hα : 0 < α)
    (hx : ∀ j ≤ k, x j ∈ interior (AubinLipschitz.effDom w))
    (hxk : x (k + 1) ∈ closure (AubinLipschitz.effDom w))
    (hmin : ∀ y ∈ closure (AubinLipschitz.effDom w),
      Phik w f h J τd α x k (x (k + 1)) ≤ Phik w f h J τd α x k y) :
    ∀ z ∈ AubinLipschitz.effDom w, Phi f h (x (k + 1)) ≤
      Phi f h z + ((1 / α : ℝ) : EReal) * bregman w z (x k)
        - ((1 / α : ℝ) : EReal) * bregman w z (x (k + 1))
        - ((1 / α : ℝ) : EReal) * bregman w (x (k + 1)) (x k)
        + Delta w Lc J ℓ τ x k := by sorry

end PLIAG
