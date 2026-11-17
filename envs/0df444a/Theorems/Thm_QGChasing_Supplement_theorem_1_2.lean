-- Prove2me | Theorems.Thm_QGChasing_Supplement_theorem_1_2
-- name    : QGChasing.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:27:52.164997+00:00
-- url     : https://prove2.me/theorems/3c5ab669-2752-41a2-a8ee-218554129ed8
-- title:
--   Theorem 1.2 — R-OBD is $(1+q^*(\lambda))$-competitive on $\mathcal Q_\lambda$ under squared movement, and no randomized algorithm does better
-- statement:
--   In convex function chasing with **squared Euclidean movement**, a learner facing hitting costs $f_1,f_2,\dots$ chooses $x_t\in X\subseteq\mathbb R^d$ and pays $\sum_{t=1}^T\big(f_t(x_t)+\frac12\|x_t-x_{t-1}\|^2\big)$. The class $\mathcal Q_\lambda$ consists of nonnegative convex costs $f_t:\mathbb R^d\to[0,\infty)$ that attain their minimum over $X$ at some $v_t\in X$ and satisfy $f_t(x)-f_t(v_t)\ge\frac\lambda2\|x-v_t\|^2$ for all $x\in X$; no smoothness is assumed. With
--   $$
--   \Lambda(q,\delta)=\frac{(1+q\delta^2)^2}{q(1-\delta^2)(q+\delta)},\qquad \phi(q)=\min_{0\le\delta<1}\Lambda(q,\delta)\qquad(q>0),
--   $$
--   let $q^*(\lambda)$ be the positive solution of $\phi(q)=\lambda$.
--
--   **Theorem.** Let $\lambda>0$.
--
--   1. There is exactly one $q>0$ with $\phi(q)=\lambda$; call it $q^*(\lambda)$.
--   2. (Upper bound) Let $q=q^*(\lambda)$, let $\delta\in[0,1)$ minimize $\Lambda(q,\cdot)$, and put $a=\frac{1+q\delta^2}{1-\delta}$, $b=\frac{a^2}{q(1+\delta)}$. For every dimension $d$, every nonempty closed convex $X\subseteq\mathbb R^d$, every $x_0\in X$ and every sequence in $\mathcal Q_\lambda$, the R-OBD path $x_t=\arg\min_{x\in X}\big\{f_t(x)+\frac a2\|x-x_{t-1}\|^2+\frac b2\|x-v_t\|^2\big\}$ satisfies, for every $T$ and every comparator $u_1,\dots,u_T\in X$ with $u_0=x_0$,
--   $$
--   \sum_{t=1}^T\Big(f_t(x_t)+\tfrac12\|x_t-x_{t-1}\|^2\Big)\ \le\ \big(1+q^*(\lambda)\big)\sum_{t=1}^T\Big(f_t(u_t)+\tfrac12\|u_t-u_{t-1}\|^2\Big).
--   $$
--   3. (Lower bound) For every $R<1+q^*(\lambda)$ there are a dimension $d$ and a horizon $T$ such that every randomized online algorithm on $\mathbb R^d$ (decision set $\mathbb R^d$, start $x_0=0$) faces some requests $f_1,\dots,f_T$, each nonnegative, convex and with $\lambda$-quadratic growth on $\mathbb R^d$ at some point, with
--   $$
--   \mathbb E_\xi[\mathrm{ALG}_T]\ >\ R\cdot\mathrm{OPT}_T ,
--   $$
--   where the expectation is over the algorithm's internal randomness and $\mathrm{OPT}_T$ is the offline optimum.
--
--   Together, the optimal competitive ratio on $\mathcal Q_\lambda$ is exactly $C^*(\lambda)=1+q^*(\lambda)$, and R-OBD attains it.
--
--   **Formalization Note** The requests in clause 3 may depend on the algorithm but not on its random seed (an oblivious adversary). $q^*(\lambda)$ is not a definition: clauses 2 and 3 are stated for every $q>0$ with $\phi(q)=\lambda$, which by clause 1 is $q^*(\lambda)$.
--
--   Differences from the source:
--   - encoding: competitive ratio 1 + q* on Q_λ (CR = ALG / min over comparators ≤ 1 + q*) → sqCost f x T ≤ (1 + q) * sqCost f u T for every u with u 0 = x₀ and u t ∈ X; reason: the ratio of nonnegative costs is at most 1 + q exactly when the bound holds against every feasible comparator; avoids a quotient with denominator 0
--   - encoding: q*(λ) is the unique positive solution of ϕ(q) = λ → clause (i) ∃! q, 0 < q ∧ phi q = lam; clauses (ii) and (iii) for every q > 0 with phi q = lam; reason: the paper presupposes existence and uniqueness when it defines q*; stating it avoids a junk value for q*
--   - encoding: ϕ(q) = min over 0 ≤ δ < 1 of Λ(q, δ); δ = argmin Λ(q, ·) → phi q = sInf of Λ(q, ·) over Set.Ico 0 1; every δ ∈ [0, 1) with bigLambda q δ = phi q; reason: the minimizer is unique (Lemma 5.2), so any minimizer is the paper's δ; the infimum equals the attained minimum
--   - encoding: R-OBD (x_t = argmin over X of f_t(x) + (a/2)‖x − x_{t−1}‖² + (b/2)‖x − v_t‖², a, b from (5)) → a hypothesis IsROBDRun (robdA q δ) (robdB q δ) X f v x₀ x; reason: the run exists and is unique (strongly convex continuous objective on a nonempty closed convex X)
--   - encoding: instances in Q_λ under Assumptions 1, 2, 4: X nonempty closed convex; f_t : ℝᵈ → [0, ∞) convex; f_t attains its minimum over X at v_t ∈ X with λ-quadratic growth on X → IsClosed X, Convex ℝ X, x₀ ∈ X; 0 ≤ f t y and ConvexOn ℝ univ (f t) for t ≥ 1; v t ∈ X and HasQuadGrowthOn lam X (f t) (v t); reason: nonemptiness follows from x₀ ∈ X; with λ > 0 quadratic growth on X at v_t ∈ X makes v_t the minimizer over X; same instances
--   - encoding: ℝᵈ; rounds t = 1, …, T → EuclideanSpace ℝ (Fin d); t + 1 for t ∈ Finset.range T, f 0 unused; reason: Lean conventions; same instances
--   - encoding: randomized online algorithm with internal randomness ξ; E_ξ[ALG_T] → seed space Ω : Type with a probability measure P and decisions x ω f t, starting at 0, nonanticipative and measurable in ω (IsRandOnlineAlg); expSqCost = ∫⁻ ω, ofReal (sqCost f (x ω f) T) ∂P; reason: the expectation over ξ requires measurable decisions; the lower Lebesgue integral counts a divergent expected cost as +∞
--   - encoding: lower bound: competitive ratio of any randomized algorithm ≥ 1 + q*, i.e. sup over instances of E_ξ[ALG_T]/OPT_T ≥ 1 + q* → for every R < 1 + q an instance with ENNReal.ofReal (R * sqOpt f 0 T) < expSqCost P x f T, the requests nonnegative, convex and with ∃ v, HasQuadGrowth lam (f t) v for 1 ≤ t ≤ T, X = ℝᵈ, x₀ = 0; reason: a supremum is at least 1 + q exactly when every R < 1 + q is exceeded; this is the paper's own restatement on p.12; X = ℝᵈ and x₀ = 0 are the setting of §5.2
--   - generalization: Lemma 5.3: inf over algorithms A defined on all spaces of D (ℝᵈ for every d ≥ 1 and H∞) of sup over T, H ∈ D and instances → ∃ d T before ∀ algorithm on EuclideanSpace ℝ (Fin d) for horizon T (which may depend on d and T); reason: Appendix A.7 proves this order (d = T + L + 1, L and T depending only on λ and R, independent of the algorithm); a dimension-uniform algorithm restricted to ℝᵈ and horizon T is such an algorithm, so the statement implies Lemma 5.3 and the lower bound of Theorem 1.2
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), Theorem 1.2, p.2 (with Eq. (2), p.2; Assumptions 1, 2, 4, p.4; §5.1, Eq. (5) and Lemma 5.1, p.9; Lemma 5.2, p.11; Lemma 5.3, p.12; Appendix A.7, pp.20–30)

import Mathlib
import Definitions.Def_QGChasing_HasQuadGrowth
import Definitions.Def_QGChasing_Supplement_bigLambda
import Definitions.Def_QGChasing_Supplement_phi
import Definitions.Def_QGChasing_Supplement_HasQuadGrowthOn
import Definitions.Def_QGChasing_Supplement_robdA
import Definitions.Def_QGChasing_Supplement_robdB
import Definitions.Def_QGChasing_Supplement_IsROBDRun
import Definitions.Def_QGChasing_Supplement_sqCost
import Definitions.Def_QGChasing_Supplement_sqOpt
import Definitions.Def_QGChasing_Supplement_IsRandOnlineAlg
import Definitions.Def_QGChasing_Supplement_expSqCost

namespace QGChasing.Supplement

/-- **Theorem 1.2** (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), p.2, with Eq. (2), p.2, Assumptions 1, 2 and 4, p.4, R-OBD and Eq. (5),
p.9, and Lemma 5.3, p.12). Squared Euclidean movement `m(x, y) = ½‖x − y‖²`, class `Q_λ`, `λ > 0`.

1. (`q*(λ)` is well defined) There is exactly one `q > 0` with `ϕ(q) = λ`.
2. (Upper bound) For every `q > 0` with `ϕ(q) = λ` and every minimizer `δ ∈ [0, 1)` of `Λ(q, ·)`,
   R-OBD with the weights `a, b` of (5) is `(1 + q)`-competitive on `Q_λ`: for every dimension `d`,
   every nonempty closed convex `X ⊆ ℝᵈ`, every `x₀ ∈ X`, every sequence of nonnegative convex
   costs `f_t : ℝᵈ → ℝ` whose minimizers `v_t ∈ X` over `X` satisfy `λ`-quadratic growth on `X`,
   every R-OBD run `x`, every horizon `T` and every comparator `u` in `X` with `u₀ = x₀`,
   `∑_{t=1}^T (f_t(x_t) + ½‖x_t − x_{t−1}‖²) ≤ (1 + q) ∑_{t=1}^T (f_t(u_t) + ½‖u_t − u_{t−1}‖²)`.
3. (Lower bound) For every `q > 0` with `ϕ(q) = λ` and every `R < 1 + q` there are a dimension `d`
   and a horizon `T` such that every randomized online algorithm on `ℝᵈ` (`X = ℝᵈ`, `x₀ = 0`) faces
   requests `f₁, …, f_T`, each nonnegative, convex and with `λ`-quadratic growth on `ℝᵈ` at some point,
   on which `E_ξ[ALG_T] > R · OPT_T`.

**Formalization Note** The competitive ratio is stated in the multiplied form against every feasible
comparator. `q*(λ)` is not a `def`: clause 1 asserts it exists uniquely and clauses 2 and 3 are
stated for every `q` with `ϕ(q) = λ`. Clause 3 fixes `d` and `T` before the algorithm (Appendix A.7
chooses `d = T + L + 1` with `L, T` depending only on `λ` and `R`); the algorithm may depend on `d`
and `T`, and the requests may depend on the algorithm but not on its seed. -/
theorem theorem_1_2 (lam : ℝ) (hlam : 0 < lam) :
    (∃! q : ℝ, 0 < q ∧ phi q = lam) ∧
    (∀ q δ : ℝ, 0 < q → phi q = lam → 0 ≤ δ → δ < 1 → bigLambda q δ = phi q →
      ∀ (d : ℕ) (X : Set (EuclideanSpace ℝ (Fin d))), IsClosed X → Convex ℝ X →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)), x₀ ∈ X →
      ∀ (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ), (∀ t, 1 ≤ t → ∀ y, 0 ≤ f t y) →
        (∀ t, 1 ≤ t → ConvexOn ℝ Set.univ (f t)) →
      ∀ (v : ℕ → EuclideanSpace ℝ (Fin d)), (∀ t, 1 ≤ t → v t ∈ X ∧ HasQuadGrowthOn lam X (f t) (v t)) →
      ∀ (x : ℕ → EuclideanSpace ℝ (Fin d)), IsROBDRun (robdA q δ) (robdB q δ) X f v x₀ x →
      ∀ (T : ℕ) (u : ℕ → EuclideanSpace ℝ (Fin d)), u 0 = x₀ → (∀ t, u t ∈ X) →
        sqCost f x T ≤ (1 + q) * sqCost f u T) ∧
    (∀ q : ℝ, 0 < q → phi q = lam → ∀ R : ℝ, R < 1 + q →
      ∃ d T : ℕ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        [MeasureTheory.IsProbabilityMeasure P]
        (x : Ω → (ℕ → EuclideanSpace ℝ (Fin d) → ℝ) → ℕ → EuclideanSpace ℝ (Fin d)),
        IsRandOnlineAlg 0 x →
        ∃ f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ,
          (∀ t, 1 ≤ t → t ≤ T → (∀ y, 0 ≤ f t y) ∧ ConvexOn ℝ Set.univ (f t) ∧
            ∃ v, QGChasing.HasQuadGrowth lam (f t) v) ∧
          ENNReal.ofReal (R * sqOpt f 0 T) < expSqCost P x f T) := by sorry

end QGChasing.Supplement
