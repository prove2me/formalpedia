-- Prove2me | Theorems.Thm_QPSpinParisi_lemma_3_2
-- name    : QPSpinParisi.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:09:19.545894+00:00
-- url     : https://prove2.me/theorems/7fa93720-0542-42eb-a959-5bab964b1675
-- title:
--   Lemma 3.2 — covariance comparison (3.3)–(3.5), and $|A^X_n-A^Y_n|\to0$ (3.6)
-- statement:
--   Let $s,t\in(S^2)^n$, $n\ge1$. Then:
--
--   1. The covariance of $X_n$ is
--   $$\mathbb E X_n(s)X_n(t)=n\sum_{p=2}^n\frac{c_p^2}{N_{n,p}}\sum_{1\le i_1<\dots<i_p\le n}\prod_{r=1}^ps_{i_r}\cdot t_{i_r}.\tag{3.3}$$
--   2. For every realization of $Y_n$,
--   $$|\mathbb E X_n(s)X_n(t)-\mathbb E Y_n(s)Y_n(t)|\le\sum_{p=2}^np(p-1)c_p^2+n\sum_{p>n}c_p^2.\tag{3.4}$$
--   3. The variances are
--   $$\mathbb E X_n(s)^2=n\sum_{p=2}^nc_p^2,\qquad\mathbb E Y_n(s)^2=n\sum_{p\ge2}c_p^2=n\xi(1).\tag{3.5}$$
--   4. For $\beta>0$,
--   $$|A^X_n(\beta)-A^Y_n(\beta)|\le\frac{\beta^2}{2n}\sum_{p=2}^np(p-1)c_p^2+\beta^2\sum_{p>n}c_p^2.\tag{3.6}$$
--   Consequently $|A^X_n(\beta)-A^Y_n(\beta)|\to0$ for every fixed $\beta>0$.
--
--   This transfers the free energy from the quantum-derived field $X_n$ to the classical field $Y_n$.
--
--   Differences from the source:
--   - generalization: $Y_n$ built as $\sum_pc_pY_{n,p}$ → every centered Gaussian field with covariance $n\xi(q(s,t))$ and continuous paths; reason: only the covariance is used; the source's field is one such field, and `exists_overlapField` makes the statement non-vacuous
--   - reading: $\sum_{p\ge2}$ in (2.1) → the sum over $p$ stops at $p=n$; reason: a $p$-local string needs $p$ distinct sites, and (3.1), (3.5) print $\sum_{p=2}^n$
--   - encoding: increasing tuples $\bar i$ and strings $\bar a$ → subsets $S$ with $|S|\ge2$ and maps $S\to$ `Fin 3`; reason: the same index set
--   - encoding: $s,t$ the Bloch vectors of product states → all $s,t\in(S^2)^n$; reason: by Lemma 3.1 these are the same points
--   - encoding: $\sup_{s,t}$ in (3.4) → the bound for each $s,t$; reason: the same statement
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.2, pp.11–12 (PDF pp.11–12)

import Mathlib
import Definitions.Def_QPSpinParisi_MixHyp
import Definitions.Def_QPSpinParisi_AX
import Definitions.Def_QPSpinParisi_AY
import Definitions.Def_QPSpinParisi_gaussMeas

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.2, pp.11–12, PDF pp.11–12: the covariance identity (3.3), the comparison (3.4), the variances (3.5), the free
energy comparison (3.6), and `|A^X_n(β) - A^Y_n(β)| → 0` for every fixed `β > 0`.

**Formalization Note** The statement is for all `s, t ∈ (S²)ⁿ`, which by `lemma_3_1` are exactly the Bloch vectors of product states.
`∑_{p>n} c_p²` is the series with the terms `p ≤ n` set to `0`. `F` is an arbitrary realization of `Y_n`. -/
theorem lemma_3_2 (c : ℕ → ℝ) (hc : MixHyp c) :
    (∀ (n : ℕ), 1 ≤ n → ∀ s t : RGGDetect.Config n 3,
      ∫ α, Xn c n α s * Xn c n α t ∂(gaussMeas n) =
        (n : ℝ) * ∑ p ∈ Finset.Icc 2 n, (c p ^ 2 / (Nat.choose n p : ℝ)) *
          ∑ S ∈ Finset.powersetCard p (Finset.univ : Finset (Fin n)), ∏ i ∈ S, RGGDetect.ip (s i) (t i)) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ (F : OverlapField c n) (s t : RGGDetect.Config n 3),
      |(∫ α, Xn c n α s * Xn c n α t ∂(gaussMeas n)) - ∫ ω, F.Y s ω * F.Y t ω ∂F.P| ≤
        (∑ p ∈ Finset.Icc 2 n, (p : ℝ) * ((p : ℝ) - 1) * c p ^ 2) +
          (n : ℝ) * ∑' p : ℕ, if n < p + 2 then c (p + 2) ^ 2 else 0) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ (F : OverlapField c n) (s : RGGDetect.Config n 3),
      (∫ α, Xn c n α s ^ 2 ∂(gaussMeas n) = (n : ℝ) * ∑ p ∈ Finset.Icc 2 n, c p ^ 2) ∧
      (∫ ω, F.Y s ω ^ 2 ∂F.P = (n : ℝ) * ∑' p : ℕ, c (p + 2) ^ 2) ∧
      ∑' p : ℕ, c (p + 2) ^ 2 = xiS c 1) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ (F : OverlapField c n) (β : ℝ), 0 < β →
      |AX c n β - AY F β| ≤
        (β ^ 2 / (2 * (n : ℝ))) * (∑ p ∈ Finset.Icc 2 n, (p : ℝ) * ((p : ℝ) - 1) * c p ^ 2) +
          β ^ 2 * ∑' p : ℕ, if n < p + 2 then c (p + 2) ^ 2 else 0) ∧
    (∀ (F : ∀ n, OverlapField c n) (β : ℝ), 0 < β →
      Tendsto (fun n => |AX c n β - AY (F n) β|) atTop (𝓝 0)) := by sorry

end QPSpinParisi
