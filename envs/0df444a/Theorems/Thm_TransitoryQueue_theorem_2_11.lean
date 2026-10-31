-- Prove2me | Theorems.Thm_TransitoryQueue_theorem_2_11
-- name    : TransitoryQueue.theorem_2_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:04:48.032367+00:00
-- url     : https://prove2.me/theorems/6f182b62-4907-4982-bea4-03e4354fc199
-- title:
--   Theorem 2.11 (corrected: Assumption 2.5 centring and the else-branch) — strong embedding of the queue length
-- statement:
--   Let $F_n$ ($n\ge1$) and $G$ be distribution functions supported on $[0,\infty)$ with $\sup_{t\ge0}|F_n(t)-G(t)|=O(1/\sqrt n)$, let $p\in[0,1]$, and let $\nu$ be a law on $[0,\infty)$ whose moment generating function is finite near $0$, with mean $\mu>0$ and standard deviation $\sigma$. Let $c_n>0$ be any sequence of server efficiencies. Then there is a probability space carrying a version of the RS$(G,p)/G/1$ model — arrival epochs $T_{n,i}$ iid $F_n$, turn-up indicators $\zeta_{n,i}$ iid Bernoulli($p$), service requirements $V_{n,i}$ iid $\nu$, standard Brownian motions $B$ and $\hat B$ common to all $n$, Brownian bridges $B^{\mathrm{br},n}$, with the blocks $(T,B^{\mathrm{br},n})$, $(\zeta,\hat B)$, $(V,B)$ independent — such that the queue length $Q_n$ satisfies, almost surely,
--
--   $$\sup_{t\in[0,\infty)}\bigl|Q_n(t)-\phi(X_n)(t)\bigr|=O\bigl(n^{1/4}\sqrt{\log n}\bigr),$$
--
--   where $\phi$ is the reflection map and
--
--   $$X_n(t)=H_n(t)-\frac{c_nt}{\mu}+\sqrt n\,\frac\sigma\mu B_{E_n(t)},\qquad E_n(t)=\frac{c_nt}{n\mu}+p\,r_n(G)+\inf_{s\le t}\Bigl(pG(s)-\frac{c_n}{n}\frac s\mu\Bigr),$$
--
--   $$H_n(t)=npF_n(t)+\sqrt n\Bigl(pB^{\mathrm{br},n}_{G(t)}+\sqrt{p(1-p)}\,\hat B_{G(t)}\Bigr).$$
--
--   Precisely: for almost every $\omega$ there is $C(\omega)$ with $|Q_n(t)-\phi(X_n)(t)|\le C\,n^{1/4}\sqrt{\log n}$ for all $n\ge2$ and $t\ge0$.
--
--   The queue length of a nonstationary, non-Markovian single-server queue fed by a finite population is thus within $O(n^{1/4}\sqrt{\log n})$ of a reflected nonstationary Gaussian process, on a sample-path basis and uniformly in time.
--
--   **Formalization Note** $Q_n$ is defined by (6), $D_n(t)$ as the Lebesgue measure of the time in $[0,t]$ the workload $\phi(W_n-c_n\cdot\mathrm{id})$ is positive. $F_n=G$ gives Assumption 2.1 exactly (then $r_n=0$ and $H_n$, $E_n$ are the printed ones); $F_n=G^{(n)}$ gives Assumption 2.5.
--
--   Differences from the source:
--   - correction: under Assumption 2.5, H_n centred at np(G(t) + r_n(G)) (through Theorem 2.8) → H_n centred at npF_n(t) = npG^{(n)}(t); reason: with G = 1 − e^{−t}, G^{(n)} = (1 − n^{−1/2})G + n^{−1/2}(1 − e^{−2t}) (Assumption 2.5 holds, r_n(G) = 1/(4√n)), c_n ≡ 1 and t = ln 2, the printed bound would force (A_n(t) − npG(t))/√n − Z_n → 0 with Z_n centred Gaussian, but (A_n(t) − npG(t))/√n has limit mean p/4
--   - correction: "Else we have sup_t |Q_n(t) − φ(X_n)(t)| = a.s. O(n^{1/4} √(log c_n))" when not (c_n = O(n^m) for some m > 0 and liminf c_n > 0) → rate n^{1/4} √(log n) for every positive sequence c_n; reason: the else clause is false as printed: for c_n = 1/n the rate is the square root of a negative number, and for c_n = 1 (n even), e^n (n odd) the rate is 0 at even n, asserting Q_n = φ(X_n) although Q_n is integer-valued and φ(X_n)(t) has a continuous law
--   - generalization: rate √(log n) only when c_n = O(n^m) for some m > 0 and liminf c_n > 0; rate √(log c_n) for super-polynomial c_n (Remark 2.12) → rate √(log n) for every sequence c_n > 0; reason: implies the first branch, and for super-polynomial c_n, log n ≤ log c_n eventually, so it implies the intended second branch
--   - generalization: two cases: Assumption 2.1 (cdf G) and Assumption 2.5 (G and G^{(n)} strictly increasing and Lipschitz, Lipschitz constant of G^{(n)} polynomial in n, r_n(G) = O(1/√n)) → distribution functions F_n, G supported on [0, ∞) with r_n = sup_t |F_n − G| = O(1/√n), no monotonicity or Lipschitz condition; reason: F_n = G is Assumption 2.1 with r_n = 0 and the printed H_n, E_n; F_n = G^{(n)} is Assumption 2.5
--   - generalization: the existence of a version (independence of the Gaussian processes not stated) → the version also has the blocks (T, B^{br,n}), (ζ, B̂), (V, B) mutually independent; reason: a more informative conclusion; it specializes to the printed one by forgetting the independence
--   - reading: "Let B, B̂ be the Brownian motions B^{br,n} the Brownian bridge processes as considered in Theorems 2.8 and 2.10" → one B and one B̂ for all n, a bridge B^{br,n} for each n; reason: the stronger reading; if the Brownian motions could also vary with n, an a.s. O bound would reduce to tightness
--   - encoding: µ the mean of a non-negative service law → 0 < µ assumed; reason: µ = 0 means V ≡ 0, and then c_n t/µ is undefined
--   - encoding: D_n(t), "the amount of time the queue stays busy till time t" → Lebesgue measure of {s ∈ [0, t] : φ(W_n − c_n·id)(s) > 0}; reason: the paper defines D_n only in words, for the non-idling server of §2.1
--   - encoding: a.s. O(n^{1/4} √log n), sup over t ∈ [0, ∞) → ∀ᵐ ω, ∃ C, ∀ n ≥ 2, ∀ t ≥ 0; reason: n = 1 is excluded since log 1 = 0; C depends on ω
--   - encoding: Brownian motions evaluated at real times G(t), E_n(t) → B, B̂ with time in ℝ≥0, evaluated at Real.toNNReal of G(t) and E_n(t); reason: G(t) ∈ [0, 1] and E_n(t) ≥ 0, so the truncation is never active
--   - encoding: mgf in a neighbourhood of 0; non-negative V_i → ∃ δ > 0, e^{ly} integrable for |l| < δ; ν(−∞, 0) = 0; reason: same conditions
-- source:
--   Chakraborty and Honnappa, Strong Embeddings for Transitory Queueing Models, arXiv:1906.06740v1, Theorem 2.11, p.8

import Mathlib
import Definitions.Def_TransitoryQueue_IsArrivalCDF
import Definitions.Def_TransitoryQueue_rn
import Definitions.Def_TransitoryQueue_queue
import Definitions.Def_TransitoryQueue_reflect
import Definitions.Def_TransitoryQueue_Xn
import Definitions.Def_TransitoryQueue_IsRSVersion
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TransitoryQueue

/-- **Theorem 2.11 (strong embedding of the queue length).** Let `F_n`, `G` be distribution
functions supported on `[0, ∞)` with `sup_t |F_n(t) - G(t)| = O(1/√n)`, let `p ∈ [0, 1]`, let `ν`
be a law on `[0, ∞)` with a finite moment generating function near `0`, mean `μ > 0` and standard
deviation `σ`, and let `c_n > 0` be server efficiencies. Then there is a version of the model
(`IsRSVersion`: arrival epochs iid `F_n`, turn-up indicators iid Bernoulli(`p`), service times iid
`ν`, Brownian motions `B`, `B̂` common to all `n`, Brownian bridges `B^{br,n}`, three independent
blocks) such that almost surely
`sup_{t ≥ 0} |Q_n(t) - φ(X_n)(t)| = O(n^{1/4} √(log n))`, with
`X_n(t) = H_n(t) - c_n t/μ + √n (σ/μ) B_{E_n(t)}`.
Chakraborty and Honnappa, *Strong Embeddings for Transitory Queueing Models*, arXiv:1906.06740v1, Theorem 2.11, p.8.

**Formalization Note** `a.s. O(·)`: for almost every `ω` there is `C(ω)` with the bound for all
`n ≥ 2` and `t ≥ 0` (`log 1 = 0`). One statement covers Assumption 2.1 (`F_n = G`, `r_n = 0`)
and Assumption 2.5 (`F_n = G^{(n)}`), with `H_n` centred at `n p F_n(t)` (the printed
`n p (G + r_n(G))` is false). The rate `√(log n)` is asserted for every positive sequence `c_n`,
which implies both printed branches. -/
theorem theorem_2_11 (F : ℕ → ℝ → ℝ) (G : ℝ → ℝ) (hF : ∀ n, IsArrivalCDF (F n)) (hG : IsArrivalCDF G)
    (hr : ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n → rn (F n) G ≤ K / Real.sqrt n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Set.Iio 0) = 0)
    (hmgf : ∃ δ : ℝ, 0 < δ ∧ ∀ l : ℝ, |l| < δ → Integrable (fun y => Real.exp (l * y)) ν)
    (hμ : 0 < ∫ y, y ∂ν)
    (c : ℕ → ℝ) (hc : ∀ n : ℕ, 1 ≤ n → 0 < c n) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (T : (n : ℕ) → Fin n → Ω → ℝ) (ζ : (n : ℕ) → Fin n → Ω → ℕ) (V : (n : ℕ) → Fin n → Ω → ℝ)
      (B Bh : ℝ≥0 → Ω → ℝ) (Bbr : ℕ → ℝ → Ω → ℝ),
      IsRSVersion P F p ν T ζ V B Bh Bbr ∧
      ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ t : ℝ, 0 ≤ t →
        |queue (c n) (fun i => T n i ω) (fun i => ζ n i ω) (fun i => V n i ω) t
            - reflect (fun u => Xn F G p (∫ y, y ∂ν) (Real.sqrt (variance id ν)) (c n) n (Bbr n)
                Bh B u ω) t|
          ≤ C * (n : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt (Real.log n) := by sorry

end TransitoryQueue
