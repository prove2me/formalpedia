-- Prove2me | Theorems.Thm_TransitoryQueue_proposition_5_2
-- name    : TransitoryQueue.proposition_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:01:44.407198+00:00
-- url     : https://prove2.me/theorems/81b65816-d016-4fc6-8485-2c59d6557a85
-- title:
--   Proposition 5.2 and Corollary 5.4 — the empirical process of a general distribution, same constants
-- statement:
--   Let $U_1,\dots,U_n$ ($n\ge1$) be iid $U[0,1]$ and $Y$ a Brownian bridge on the same probability space, and suppose the uniform empirical process satisfies (16) with constants $C,K,\lambda$: for all $x>0$,
--
--   $$P\Bigl(\sup_{s\in[0,1]}\sqrt n\,\bigl|\sqrt n(F_n(s)-s)-Y(s)\bigr|>C\log n+x\Bigr)<Ke^{-\lambda x}.$$
--
--   Let $F$ be any distribution function supported on $[0,\infty)$ and $T_i=F^{\leftarrow}(U_i)$. Then $T_1,\dots,T_n$ are iid with distribution function $F$, and with the same constants, for all $x>0$,
--
--   $$P\Bigl(\sup_{t\ge0}\bigl|\sqrt n\,(G_n(t)-F(t))-Y(F(t))\bigr|>C\frac{\log n}{\sqrt n}+x\Bigr)<Ke^{-\lambda x\sqrt n},$$
--
--   where $G_n(t)=\frac1n\#\{i:T_i\le t\}$. With $F=G$ this is Proposition 5.2 (64); with $F=G^{(n)}$ it is Corollary 5.4; that the constants are unchanged is Remark 5.3.
--
--   Differences from the source:
--   - generalization: G of Assumption 2.1 with p = 1 (Proposition 5.2) or G^{(n)} of Assumption 2.5 (Corollary 5.4) → any distribution function F supported on [0, ∞); reason: F = G and F = G^{(n)} are the two printed cases; strict monotonicity, Lipschitz continuity and continuity are not needed with the version T_i = F^←(U_i)
--   - generalization: "there exists a Brownian bridge B^{br,n} and a version of T_1, …, T_n along with constants C_2, K_2, λ_2" → every bridge–uniform coupling satisfying (16) with constants (C, K, λ) yields, through T_i = F^←(U_i), a version satisfying (64) with the same constants; reason: a statement for every coupling satisfying (16) (the proof's construction, pp.24–26, and Remark 5.3); such a coupling exists by theorem_3_2 (Remark 8.3), and then this item gives the printed existence of a bridge, a version and constants
--   - encoding: P(sup_{t ≥ 0} … > a) → P of the event that some t ≥ 0 exceeds a; reason: the same event
-- source:
--   Chakraborty and Honnappa, Strong Embeddings for Transitory Queueing Models, arXiv:1906.06740v1, Proposition 5.2, eq. (64), p.24; Remark 5.3, p.26; Corollary 5.4, p.26

import Mathlib
import Definitions.Def_TransitoryQueue_IsArrivalCDF
import Definitions.Def_TransitoryQueue_IsBrownianBridge
import Definitions.Def_TransitoryQueue_quantile
open MeasureTheory ProbabilityTheory

namespace TransitoryQueue

/-- **Proposition 5.2 and Corollary 5.4 (strong embedding of a general empirical process).** Let
`U_1, …, U_n` be iid `U[0,1]` and `Y` a Brownian bridge such that the uniform empirical process
satisfies (16) with constants `C, K, λ`: `P(sup_{s∈[0,1]} √n |α_n(s) - Y(s)| > C log n + x) < K e^{-λx}`
for `x > 0`. Let `F` be a distribution function supported on `[0, ∞)` and `T_i = F^←(U_i)`. Then
`T_1, …, T_n` are iid with distribution function `F`, and with the same constants, for all `x > 0`,
`P(sup_{t ≥ 0} |√n (G_n(t) - F(t)) - Y(F(t))| > C log n/√n + x) < K e^{-λ x √n}`, where
`G_n(t) = n^{-1} #{i : T_i ≤ t}`.
Chakraborty and Honnappa, *Strong Embeddings for Transitory Queueing Models*, arXiv:1906.06740v1, Proposition 5.2, p.24, eq. (64), Remark 5.3, p.26 (the same constants), and Corollary 5.4,
p.26.

**Formalization Note** `F = G` is Proposition 5.2, `F = G^{(n)}` is Corollary 5.4. The version
`T_i = F^←(U_i)` is the paper's construction; it needs no continuity of `F`. "sup > a" is written
"some time has value > a". -/
theorem proposition_5_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n) (U : Fin n → Ω → ℝ) (Y : ℝ → Ω → ℝ)
    (hU_law : ∀ i, HasLaw (U i) (volume.restrict (Set.Icc (0 : ℝ) 1)) P)
    (hU_indep : iIndepFun U P) (hY : IsBrownianBridge Y P)
    (C K lam : ℝ)
    (hKMT : ∀ x : ℝ, 0 < x →
      P.real {ω | ∃ s ∈ Set.Icc (0 : ℝ) 1, C * Real.log n + x <
          Real.sqrt n * |Real.sqrt n *
            (((Finset.univ.filter (fun i : Fin n => U i ω ≤ s)).card : ℝ) / n - s) - Y s ω|}
        < K * Real.exp (-(lam * x)))
    (F : ℝ → ℝ) (hF : IsArrivalCDF F) :
    (∀ i, Measurable (fun ω => quantile F (U i ω)) ∧
      ∀ t : ℝ, P {ω | quantile F (U i ω) ≤ t} = ENNReal.ofReal (F t)) ∧
    iIndepFun (fun i ω => quantile F (U i ω)) P ∧
    ∀ x : ℝ, 0 < x →
      P.real {ω | ∃ t : ℝ, 0 ≤ t ∧ C * Real.log n / Real.sqrt n + x <
          |Real.sqrt n * (((Finset.univ.filter
              (fun i : Fin n => quantile F (U i ω) ≤ t)).card : ℝ) / n - F t) - Y (F t) ω|}
        < K * Real.exp (-(lam * x * Real.sqrt n)) := by sorry

end TransitoryQueue
