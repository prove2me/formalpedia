-- Prove2me | Theorems.Thm_PADMPriv_proposition_4_1
-- name    : PADMPriv.proposition_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:09:00.36731+00:00
-- url     : https://prove2.me/theorems/24675341-62e7-44bc-aa69-c147d67f5c6f
-- title:
--   Proposition 4.1 — sensitivity of the sample operators: $\|T_{f(\cdot,d)}(u)-T_{f(\cdot,d')}(u)\|_2\le L/(\beta\sqrt{\omega_A})$
-- statement:
--   Let $\{f(\cdot,d)\}_{d\in R}$ be a family of convex, differentiable and $L$-Lipschitz functions on $\mathbb R^p$, let $A\in\mathbb R^{m\times p}$ have full row rank, and let $\omega_A>0$ be the smallest eigenvalue of $AA^\top$. Then for every $u\in\mathbb R^m$ and every two records $d,d'\in R$,
--   $$
--   \big\|T_{f(\cdot,d)}(u)-T_{f(\cdot,d')}(u)\big\|_2 \le \frac{L}{\beta\sqrt{\omega_A}}.
--   $$
--   In the paper's form: for any $k$ and $u$, $\sup_{D\sim D'}\|T_{f_k}(u)-T_{f'_k}(u)\|_2\le L/(\beta\sqrt{\omega_A})$ (22). Hence Condition 1 holds with $C = L/(\beta\sqrt{\omega_A})$.
--
--   **Formalization Note** $\beta>0$. The proximal problems (13) for every $f(\cdot,d)$ are assumed to have minimizers.
--
--   Differences from the source:
--   - encoding: sup over D ∼ D′ of ‖T_{f_k}(u) − T_{f′_k}(u)‖₂ for each step k → the bound for every pair of records d, d′; reason: f_k and f′_k range exactly over the pairs f(·,d), f(·,d′); same claim
--   - encoding: the sample proximal operators P_{β,f(·,d),A} used as everywhere defined → hypothesis that (13) for f(·,d) has a minimizer for every record d and input u; reason: Algorithm 1 is undefined otherwise; excludes only undefined cases
--   - encoding: ω_A > 0 the smallest eigenvalue of AAᵀ → hypothesis 0 < m; reason: ω_A is undefined for m = 0
--   - generalization: g convex with proximal minimizers and B of full row rank (standing assumptions, pp.6-7) → g and B arbitrary; reason: the B-term of (15) is the same for both records and cancels (A.6, p.23); the source's case is an instance
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Proposition 4.1, p.9 (proof A.6, p.23)

import Mathlib
import Definitions.Def_PADMPriv_padmOp
import Definitions.Def_PADMPriv_omegaA

namespace PADMPriv

/-- Proposition 4.1 of Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), p.9 (proof A.6, p.23): if `{f(·, d)}_{d ∈ R}` is a
family of convex, differentiable and `L`-Lipschitz functions on `ℝᵖ` and `A` has full row rank,
with `ω_A > 0` the smallest eigenvalue of `AAᵀ`, then for every `u ∈ ℝᵐ` and every two records
`d, d′`, `‖T_{f(·,d)}(u) − T_{f(·,d′)}(u)‖₂ ≤ L/(β√ω_A)` (22).

**Formalization Note** The paper's `sup_{D ∼ D′} ‖T_{f_k}(u) − T_{f′_k}(u)‖₂` at step `k` ranges
over the pairs `(f(·, d₍ₖ₎), f(·, d′₍ₖ₎))`, i.e. over every pair of records, so the bound is stated
for every pair `d, d′`. `β > 0`; `m ≥ 1` (`ω_A` is defined only then); the proximal problems (13)
for every `f(·, d)` are assumed to have minimizers, so that `T_{f(·,d)}` is defined. -/
theorem proposition_4_1 {m p l : ℕ} {R : Type*} (hm : 0 < m) (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin l) ℝ) (c : EuclideanSpace ℝ (Fin m)) (hA : A.rank = m)
    (f : EuclideanSpace ℝ (Fin p) → R → ℝ) (g : EuclideanSpace ℝ (Fin l) → ℝ) (L : NNReal)
    (hfconv : ∀ d, ConvexOn ℝ Set.univ (fun x => f x d))
    (hfdiff : ∀ d, Differentiable ℝ (fun x => f x d))
    (hfLip : ∀ d, LipschitzWith L (fun x => f x d)) (β : ℝ) (hβ : 0 < β)
    (hfprox : ∀ d u, ∃ x, IsProxMin β (fun x => f x d) A u x)
    (d d' : R) (u : EuclideanSpace ℝ (Fin m)) :
    ‖padmOp β (fun x => f x d) g A B c u - padmOp β (fun x => f x d') g A B c u‖ ≤
      (L : ℝ) / (β * Real.sqrt (omegaA A)) := by sorry

end PADMPriv
