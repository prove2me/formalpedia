-- Prove2me | Theorems.Thm_StochApproxDyn_WeakAPT_Supplement_robbinsMonro_not_tendsto_normallyRepelling
-- name    : StochApproxDyn.WeakAPT.Supplement.robbinsMonro_not_tendsto_normallyRepelling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:19:37.769497+00:00
-- url     : https://prove2.me/theorems/51a9e625-c7eb-4e2d-810b-6dba9f84c33e
-- title:
--   Theorem 9.1 (corrected: adapted initial data) — bounded exciting Robbins–Monro noise avoids normally repelling sets
-- statement:
--   Assume the standing assumptions of §9: $F:\mathbb R^m\to\mathbb R^m$ generates the flow $\Phi$; $S\subseteq\mathbb R^m$ is an embedded $(m-d)$-dimensional submanifold, $1\le d\le m$; $\Gamma\subseteq S$ is nonempty, compact and invariant; $S$ is locally invariant ($\Phi_t(U\cap S)\subseteq S$ for $|t|\le t_0$, $U$ a neighbourhood of $\Gamma$); and for $p\in\Gamma$, $\mathbb R^m=T_pS\oplus E^u_p$ with $p\mapsto E^u_p$ continuous into $G(d,m)$, $D\Phi_t(p)E^u_p=E^u_{\Phi_t(p)}$, and $\|D\Phi_t(p)w\|\ge Ce^{\lambda t}\|w\|$ for $w\in E^u_p$, $t\ge0$, with $\lambda,C>0$.
--
--   Let $\{x_n\}$ given by (7), $x_{n+1}-x_n=\gamma_{n+1}(F(x_n)+U_{n+1})$, be a Robbins–Monro algorithm (§4.2), with $x_0$ $\mathcal F_0$-measurable. Assume:
--
--   1. there is $K>0$ with $\|U_n\|\le K$ for all $n\ge0$;
--   2. $\{\gamma_n\}$ is as in Proposition 4.4: $\sum_ne^{-c/\gamma_n}<\infty$ for each $c>0$;
--   3. there are a neighbourhood $\mathcal N(\Gamma)$ of $\Gamma$ and $b>0$ such that for every unit vector $v\in\mathbb R^m$ and every $n$, $E(\langle U_{n+1},v\rangle^+\mid\mathcal F_n)\ge b\mathbf 1_{\{x_n\in\mathcal N(\Gamma)\}}$;
--   4. there is $0<\alpha\le1$ such that (a) $F$ and $S$ are $C^{1+\alpha}$ and (b)
--   $$\lim_{n\to\infty}\frac{\gamma_{n+1}^\alpha}{\sqrt{\lim_{m\to\infty}\sum_{i=n+1}^m\gamma_i^2}}=0.$$
--
--   Then
--
--   $$P\Big(\lim_{n\to\infty}d(x_n,\Gamma)=0\Big)=0.$$
--
--   The theorem covers linearly unstable equilibria, linearly unstable periodic orbits and more general normally repelling sets, and both $\sum\gamma_n^2<\infty$ and $\sum\gamma_n^2=\infty$ (in the latter case the denominator in 4(b) is infinite and the condition holds for every $\alpha>0$, Remark 9.2).
--
--   **Formalization Note** The requirement that $x_0$ be $\mathcal F_0$-measurable is an explicit correction to the printed hypotheses, which adapt only the noise. It excludes anticipating initial conditions; the counterexample and the source proof requiring adapted iterates are recorded in `DISPROOF.md` and `SOURCE_AUDIT.json`. The submanifold is given by $C^{1+\alpha}$ slice charts, $T_pS$ by velocities of curves in $S$, and continuity into $G(d,m)$ by continuity of the orthogonal projection onto $E^u_p$. The tail $\sum_{i>n}\gamma_i^2$ and the ratio in 4(b) are computed in $[0,\infty]$. The conditional expectation in 3 is of a bounded, hence integrable, variable.
--
--   Differences from the source:
--   - correction: "a stochastic process $\{x_n\}$ given by (7)" with conditioning on $\mathcal F_n$ → $x_0$ is $\mathcal F_0$-measurable; reason: without it the statement is false: for $F(x)=x$ on $\mathbb R$, $\Gamma=\{0\}$, i.i.d. signs $U_n$ and $\gamma_n=1/n$, the anticipating start $x_0=-\sum_{k\ge1}\gamma_kU_k/\prod_{j\le k}(1+\gamma_j)$ gives $x_n\to0$ almost surely while all printed hypotheses hold.
--   - generalization: "$C^{1+\alpha}$: $C^1$ and its derivative is $\alpha$-Hölder" (p. 49) → the derivative of $F$ is locally $\alpha$-Hölder; reason: a globally Hölder derivative is locally Hölder, and the theorem only involves $F$ near the compact set $\Gamma$.
--   - encoding: $e^{-c/\gamma_n}$ at $\gamma_n=0$ → the term $0$; reason: its value as a limit; Lean's $c/0=0$ would make it $1$.
--   - encoding: $\sqrt{\lim_{m}\sum_{i=n+1}^m\gamma_i^2}$ and the ratio → computed in $[0,\infty]$; reason: an infinite tail gives ratio $0$, as in Remark 9.2.
--   - correction: §9(ii) prints $p\in E_p^u$ for a base point → $p\in\Gamma$; reason: the preceding sentence defines the splitting over every $p\in\Gamma$, and the fiber vectors are $w$ in (iii).
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 49, Theorem 9.1 (standing assumptions of §9, pp. 47–48; Robbins–Monro algorithm, §4.2, p. 14; Proposition 4.4, p. 16; Remark 9.2, p. 49)

import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_RobbinsMonro
import Definitions.Def_StochApproxDyn_WeakAPT_Supplement_NormallyRepelling

open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace

namespace StochApproxDyn.WeakAPT.Supplement

/-- Theorem 9.1 (Benaïm 1999, p. 49), corrected to require adapted initial data. Assume the setting of §9: `F : ℝ^m → ℝ^m` generates the
flow `Φ`, `S` is an `(m − d)`-dimensional embedded submanifold (`1 ≤ d ≤ m`), and `Γ ⊆ S` is a
nonempty compact invariant set, with `S` locally invariant near `Γ` and a continuous invariant
splitting `ℝ^m = T_p S ⊕ E^u_p` (`p ∈ Γ`) on which `DΦ_t` expands uniformly at an exponential rate.
Let `{x_n}` given by (7), `x_{n+1} − x_n = γ_{n+1}(F(x_n) + U_{n+1})`, be a Robbins–Monro
algorithm (§4.2), `x_0` being `ℱ_0`-measurable. Assume:
(i) there exists `K > 0` with `‖U_n‖ ≤ K` for all `n ≥ 0`;
(ii) `{γ_n}` is as in Proposition 4.4: `∑_n e^{−c/γ_n} < ∞` for each `c > 0`;
(iii) there exist a neighbourhood `𝒩(Γ)` of `Γ` and `b > 0` such that for every unit vector
`v ∈ ℝ^m`, `E(⟨U_{n+1}, v⟩⁺ | ℱ_n) ≥ b 1_{x_n ∈ 𝒩(Γ)}`;
(iv) there exists `0 < α ≤ 1` such that (a) `F` and `S` are `C^{1+α}` and
(b) `lim_{n → ∞} γ_{n+1}^α / √(lim_{m → ∞} ∑_{i=n+1}^m γ_i²) = 0`.
Then `P(lim_{n → ∞} d(x_n, Γ) = 0) = 0`.

The requirement that `x_0` is `ℱ_0`-measurable repairs an omitted assumption: the
printed martingale-difference conditions alone allow an anticipating initial condition
for which convergence to an unstable equilibrium has probability one. See the chunk
source audit and DISPROOF.md for the counterexample and the excluded cases.

In (ii) the term `e^{−c/γ_n}` is read as `0` when `γ_n = 0`. In (iv)(b) the tail sum is computed
in `[0, ∞]`, so that when `∑ γ_i² = ∞` the denominator is `∞` and the ratio is `0` (Remark 9.2). -/
theorem robbinsMonro_not_tendsto_normallyRepelling {m d : ℕ} {Ω : Type*}
    {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (Φ : Flow ℝ (EuclideanSpace ℝ (Fin m))) (S Γ U : Set (EuclideanSpace ℝ (Fin m))) (t₀ : ℝ)
    (Eu : EuclideanSpace ℝ (Fin m) → Submodule ℝ (EuclideanSpace ℝ (Fin m)))
    (hNR : IsNormallyRepellingSet d F Φ S Γ U t₀ Eu)
    (γ : ℕ → ℝ) (x Un : ℕ → Ω → EuclideanSpace ℝ (Fin m))
    (hRM : StochApproxDyn.MartingaleNoise.IsRobbinsMonro P ℱ F γ x Un)
    (hx0 : StronglyMeasurable[ℱ 0] (x 0))
    (h_i : ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (ω : Ω), ‖Un n ω‖ ≤ K)
    (h_ii : ∀ c : ℝ, 0 < c →
      Summable (fun n : ℕ => if 0 < γ (n + 1) then Real.exp (-c / γ (n + 1)) else 0))
    (h_iii : ∃ NΓ ∈ nhdsSet Γ, ∃ b : ℝ, 0 < b ∧ ∀ v : EuclideanSpace ℝ (Fin m), ‖v‖ = 1 →
      ∀ n : ℕ, ∀ᵐ ω ∂P, b * NΓ.indicator (fun _ => (1 : ℝ)) (x n ω) ≤
        (P[fun ω => max ⟪Un (n + 1) ω, v⟫_ℝ 0 | ℱ n]) ω)
    (h_iv : ∃ α : ℝ≥0, 0 < α ∧ α ≤ 1 ∧ IsC1HolderOn α F Set.univ ∧
      IsC1HolderSubmanifold α d S ∧
      Tendsto (fun n : ℕ => ENNReal.ofReal (γ (n + 1) ^ (α : ℝ)) /
          (∑' i : ℕ, ENNReal.ofReal (γ (n + 1 + i) ^ 2)) ^ (1 / 2 : ℝ)) atTop (nhds 0)) :
    P {ω | Tendsto (fun n => Metric.infDist (x n ω) Γ) atTop (nhds 0)} = 0 := by sorry

end StochApproxDyn.WeakAPT.Supplement
