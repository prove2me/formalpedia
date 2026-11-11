-- Prove2me | Theorems.Thm_QaryCVP_lemma_4_5
-- name    : QaryCVP.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:01:01.484872+00:00
-- url     : https://prove2.me/theorems/da1c0c1d-ac99-4563-9426-d5baef90b859
-- title:
--   Lemma 4.5 — one correction attempt: $\Pr[\text{success}]\ge p/2$ and $\|\mathbb E[w\mid\text{success}]\|\le\varepsilon\sqrt d$ for every $s$
-- statement:
--   Fix a rational $0<\beta<1$ and constants $p\in(0,1)$, $\varepsilon>0$, $\alpha_0>0$, $D>0$. For integers $q\ge2$, $m\ge1$, $n\ge1$, $d$ with $\alpha_0n\le d\le n$ and $\delta n\le Dd$, put $\ell=\lceil d^{2/3}\rceil$, $\ell'=\lceil\ell/\beta\rceil$, $n_0=d-\ell-\ell'>0$. Let a randomized short solver on $A\in(\mathbb Z/q\mathbb Z)^{m\times n_0}$, $t\in(\mathbb Z/q\mathbb Z)^m$ return $\bot$ or $v\in\mathbb Z^{n_0}$ with $Av=t$, $\|v\|^2\le\beta n_0$, and assume all but a $2^{-\Omega(n_0^{2/3})}$ fraction of matrices have average success at least $p$ over independent uniform $t$ and solver randomness. Partition the first $d$ columns of $H$ as in Algorithm 3 and use this solver in one correction attempt. Then:
--
--   1. for all sufficiently large $n$, all but a $2^{-\Omega(n^{2/3})}$ fraction of $H\in(\mathbb Z/q\mathbb Z)^{m\times n}$ satisfy, simultaneously for every $s\in(\mathbb Z/q\mathbb Z)^m$,
--
--   $$\Pr[\text{success}]\ge p/2,\qquad\|\mathbb E[w\mid\text{success}]\|\le\varepsilon\sqrt d;$$
--
--   2. every successful output is supported on the first $d$ coordinates and satisfies $Hw=s$ and $\|w\|^2\le\beta d$.
--
--   **Formalization Note** The solver is a family of randomized functions on a probability space $(\Omega,\mu)$ with measurable outcome events; it may depend on the whole instance $(q,m,n,d)$. The hypothesis is required only at the dimensions $(q,m,n_0)$ that arise from admissible $(q,m,n,d)$. $\delta n$ is $m\log_2q$.
--
--   Differences from the source:
--   - generalization: a randomized short solver (unspecified randomness) → a family of randomized functions S n d A t ω, indexed by the instance (n, d) as well as the implicit dimensions (q, m, n₀), on an arbitrary probability space (Ω, μ) with measurable outcome events; reason: covers every source of randomness and every per-instance solver; fair coins are a special case
--   - reading: all but a 2^{−Ω(f(n))} fraction / probability 1 − 2^{−Ω(f(n))} → ∃ c > 0 and a threshold N with fraction (resp. probability) ≥ 1 − 2^{−c f(n)} for n ≥ N; reason: p.12 definition of Ω for sufficiently large n (R4)
--   - encoding: fraction of matrices → count of matrices with the property divided by q^{mn}, as a real number; reason: R5; same instances
--   - reading: all but a 2^{−Ω(n₀^{2/3})} fraction of matrices (hypothesis) → ∃ c₀ > 0, N₀ such that for n₀ ≥ N₀ at every arising (q, m, n₀) the fraction is ≥ 1 − 2^{−c₀ n₀^{2/3}}; reason: uniform constants, as the uniform conclusion requires; required only where the attempt uses it
--   - encoding: j sampled with bounded bits (proof, p.38) → j uniform on [ℓ′]; reason: the lemma's attempt samples j uniformly; the bit-level sampling is an implementation detail of the proof
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Lemma 4.5, p.37

import Mathlib
import Definitions.Def_QaryCVP_qaryLattice
import Definitions.Def_QaryCVP_matAvg
import Definitions.Def_QaryCVP_corrAttempt
import Definitions.Def_QaryCVP_alg3

open MeasureTheory ProbabilityTheory

namespace QaryCVP

/-- **Lemma 4.5** (one correction attempt). Kim, Kwon, Lee, Lee, STOC 2027 submission manuscript
(sha256 9aeb2ff4…ab4), Lemma 4.5, p.37.

Fix a rational `0 < β < 1` and constants `p ∈ (0, 1)`, `ε > 0`, `α₀ > 0`, `D > 0`. Let integers
`q ≥ 2`, `m ≥ 1`, `n ≥ 1`, `d` satisfy `α₀n ≤ d ≤ n` and `δn ≤ Dd`; put `ℓ = ⌈d^{2/3}⌉`,
`ℓ′ = ⌈ℓ/β⌉`, `n₀ = d − ℓ − ℓ′ > 0`. Let a randomized short solver on `A ∈ (Z/qZ)^{m×n₀}`,
`t ∈ (Z/qZ)^m` return `⊥` or `v ∈ Z^{n₀}` with `Av = t` and `‖v‖² ≤ βn₀`, and assume all but a
`2^{−Ω(n₀^{2/3})}` fraction of matrices have average success at least `p` over independent uniform
`t` and solver randomness. Partition the first `d` columns of `H` as in Algorithm 3 and use this
solver in one correction attempt. Then:

1. for all sufficiently large `n`, all but a `2^{−Ω(n^{2/3})}` fraction of `H ∈ (Z/qZ)^{m×n}`
   satisfy, simultaneously for every `s ∈ (Z/qZ)^m`, `Pr[success] ≥ p/2` and
   `‖E[w | success]‖ ≤ ε√d`;
2. every successful output is supported on the first `d` coordinates and satisfies `Hw = s` and
   `‖w‖² ≤ βd`.

**Formalization Note.** The solver is a family of randomized functions `S n d A t ω` on a
probability space `(Ω, μ)`, with measurable outcome events; it may depend on the instance
`(q, m, n, d)` (indexed by `n` and `d`; `q`, `m`, `n₀` are the implicit dimensions), as the paper's
per-instance "a randomized short solver" allows. The `2^{−Ω(·)}` hypotheses and conclusions are
explicit `∃ c > 0, N`, uniform over `q, m, d` (R4); the hypothesis is required only at the
instances `(q, m, n₀)` that arise. `j` is uniform on `[ℓ′]` in the model; the paper's bounded-bit
sampling of `j` is an implementation detail of the proof (p.38). `δn` is `m log₂ q`. -/
theorem lemma_4_5 (β : ℚ) (hβ0 : 0 < β) (hβ1 : β < 1) (p ε α₀ D : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hε : 0 < ε) (hα₀ : 0 < α₀) (hD : 0 < D)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : ℕ → ℕ → ∀ {m n0 q : ℕ}, Matrix (Fin m) (Fin n0) (ZMod q) → (Fin m → ZMod q) → Ω →
      Option (Fin n0 → ℤ))
    (hSmeas : ∀ (n d m n0 q : ℕ) (A : Matrix (Fin m) (Fin n0) (ZMod q)) (t : Fin m → ZMod q)
      (o : Option (Fin n0 → ℤ)), MeasurableSet {ω | S n d A t ω = o})
    (hSvalid : ∀ (n d m n0 q : ℕ) (A : Matrix (Fin m) (Fin n0) (ZMod q)) (t : Fin m → ZMod q)
      ω v, S n d A t ω = some v → A.mulVec (fun j => (v j : ZMod q)) = t ∧ sqNormZ v ≤ β * n0)
    (hSsucc : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ N₀ : ℕ, ∀ q m n d : ℕ, 2 ≤ q → 1 ≤ m → 1 ≤ n →
      α₀ * n ≤ d → d ≤ n → (m : ℝ) * Real.logb 2 q ≤ D * d →
      0 < (d : ℤ) - ellOf d - ell'Of (ellOf d) β →
      N₀ ≤ d - ellOf d - ell'Of (ellOf d) β →
      let n0 := d - ellOf d - ell'Of (ellOf d) β
      1 - (2 : ℝ) ^ (-c₀ * (n0 : ℝ) ^ ((2 : ℝ) / 3)) ≤
        matFrac q m n0 (fun A =>
          p ≤ vecAvg q m (fun t => (μ {ω | (S n d A t ω).isSome}).toReal))) :
    (∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ q m n d : ℕ, N ≤ n → 2 ≤ q → 1 ≤ m →
      α₀ * n ≤ d → d ≤ n → (m : ℝ) * Real.logb 2 q ≤ D * d →
      0 < (d : ℤ) - ellOf d - ell'Of (ellOf d) β →
      1 - (2 : ℝ) ^ (-c * (n : ℝ) ^ ((2 : ℝ) / 3)) ≤
        matFrac q m n (fun H => ∀ s : Fin m → ZMod q,
          p / 2 ≤ succProb (attMeasure (ellOf d) (ell'Of (ellOf d) β) μ)
              (corrAttempt (S n d) H (d - ellOf d - ell'Of (ellOf d) β) (ellOf d)
                (ell'Of (ellOf d) β) s) ∧
          condMeanNorm (attMeasure (ellOf d) (ell'Of (ellOf d) β) μ)
              (corrAttempt (S n d) H (d - ellOf d - ell'Of (ellOf d) β) (ellOf d)
                (ell'Of (ellOf d) β) s) ≤ ε * Real.sqrt d)) ∧
    (∀ q m n d : ℕ, 2 ≤ q → 1 ≤ m → 1 ≤ n → α₀ * n ≤ d → d ≤ n →
      (m : ℝ) * Real.logb 2 q ≤ D * d → 0 < (d : ℤ) - ellOf d - ell'Of (ellOf d) β →
      ∀ (H : Matrix (Fin m) (Fin n) (ZMod q)) (s : Fin m → ZMod q)
        (a : AttSample (ellOf d) (ell'Of (ellOf d) β) Ω) (w : Fin n → ℤ),
        corrAttempt (S n d) H (d - ellOf d - ell'Of (ellOf d) β) (ellOf d) (ell'Of (ellOf d) β)
          s a = some w →
        (∀ i : Fin n, d ≤ i.val → w i = 0) ∧ H.mulVec (fun j => (w j : ZMod q)) = s ∧
          sqNormZ w ≤ β * d) := by sorry

end QaryCVP
