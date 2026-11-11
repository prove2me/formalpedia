-- Prove2me | Theorems.Thm_SumReLU_proposition_4_1
-- name    : SumReLU.proposition_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:27:40.178202+00:00
-- url     : https://prove2.me/theorems/ee99e4da-9a81-4dd3-acde-955c7e5482af
-- title:
--   Proposition 4.1 (corrected: list size poly(k/λ)(1+log(1/δ))) — polynomial-time coarse direction recovery
-- statement:
--   There is a randomized algorithm and a constant $C$ with the following guarantee. Given $d,k\ge1$, $\lambda,\delta\in(0,1)$ and i.i.d. examples $(x,f(x))$ with $x\sim N(0,I_d)$ and $f=\sum_{i=1}^k\beta_i\sigma(w_i\cdot x)\in\mathcal C_{d,k}$, on every run it
--
--   1. draws at most $N=C(d+k+1/\lambda+1/\delta)^C$ examples,
--   2. performs at most $C(d+N)^C$ operations,
--   3. outputs a list $L$ of at most $C(k/\lambda)^C(1+\log(1/\delta))$ unit vectors,
--
--   and with probability at least $1-\delta$, for every $i\in[k]$ with $\beta_i\ge\lambda$ there is $r_i\in L$ with
--   $$
--   |r_i\cdot w_i|\ge0.99 .
--   $$
--
--   This is the coarse direction recovery procedure postulated in Assumption 1, implemented with polynomial resources; it is the subroutine the main learner calls.
--
--   **Formalization Note** The algorithm is a single program of the published randomized sampling real RAM `GaussMixHH.Machine`, restricted by `SelfSelReg.ArithmeticCoin` to exact $+,-,\times,\div$, rational literals, comparisons, memory and pointer moves, a pointer-to-real cast, fair coins, `sample` and `halt` (no square root, exponential, trigonometric function, eigensolver or Gaussian draw). One `sample` writes one labeled example $(x,f(x))\in\mathbb R^{d+1}$, label last, and costs $d+1$; every other instruction costs $1$. The program and the constant $C$ are fixed before every parameter and every target. The program reads $k,\lambda,\delta$ from memory; the list is decoded from memory as the normalizations of nonzero raw vectors (exact unit vectors need a square root). The logarithm is natural.
--
--   Differences from the source:
--   - correction: $|L|=\mathrm{poly}(k/\lambda)\log(1/\delta)$ → $|L|\le C(k/\lambda)^C(1+\log(1/\delta))$; reason: the printed bound is false for $\delta$ near $1$: with $d=k=1$, $w_1=1$, $\beta_1=1$, $\lambda=1/2$ (every assumption holds) and $\delta<1$ so close to $1$ that $C'(k/\lambda)^c\log(1/\delta)<1$, the list must be empty, yet the guarantee for $i=1$ must hold with probability $1-\delta>0$; the proof's list has $2N_u=\mathrm{poly}(k/\lambda)\log(k/\delta)$ elements (p.48)
--   - reading: "there is an algorithm … runs in time" → one program of the `GaussMixHH` sampling real RAM restricted by `SelfSelReg.ArithmeticCoin`; time is the number of executed instructions, `sample` costing $d+1$; reason: the paper names no machine; arithmetic with coins and sampling is the non-weaker reading (a square-root, exponential, eigensolver or Gaussian primitive would weaken the claim)
--   - encoding: $N=\mathrm{poly}(d,k,1/\lambda,1/\delta)$, $T=\mathrm{poly}(d,N)$, $\mathrm{poly}(k/\lambda)$ → $C(d+k+1/\lambda+1/\delta)^C$, $C(d+N)^C$ and $C(k/\lambda)^C$ with one constant $C$ fixed with the program before all parameters; reason: §2, p.9 defines $\mathrm{poly}(\cdot)$ by explicit constants
--   - reading: sample count and running time → worst-case bounds on every coin tape and example stream; reason: the stronger of the two readings (worst case, not expected)
--   - encoding: "with probability at least $1-\delta$", examples, input and output → a measurable set of runs of measure at least $1-\delta$ under coins $\otimes$ i.i.d. examples; input list $[k,\lambda,\delta]$; output list read from memory and normalized, raw vectors nonzero; reason: Lean conventions for the run space and the machine's input/output
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), Proposition 4.1, p.24 (PDF p.26), restated pp.33–34 (PDF pp.35–36) and p.47 (PDF p.49); proof pp.47–48 (PDF pp.49–50)

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_SelfSelReg_ArithmeticCoin
import Definitions.Def_SumReLU_reluSum
import Definitions.Def_SumReLU_sampleLaw
import Definitions.Def_SumReLU_thetaPM
import Definitions.Def_SumReLU_cdrOutput

open MeasureTheory ProbabilityTheory

namespace SumReLU

/-- **Proposition 4.1** (Polynomial-Time CDR), with the list-size bound corrected to
`poly(k/λ)(1 + log(1/δ))`.

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), Proposition 4.1, p.24 (PDF p.26), restated pp.33–34 and p.47 (PDF pp.35–36, 49); proof
pp.47–48 (PDF pp.49–50): "Let k, d ∈ ℤ₊ and λ, δ ∈ (0, 1). Let D be a Gaussian sum of k ReLUs. Then,
there is an algorithm (CDRviaImplicitTensor(D, λ, δ)) that draws N = poly(d, k, 1/λ, 1/δ) i.i.d.
samples from D, runs in T = poly(d, N) time, and outputs a list L of unit vectors of size
|L| = poly(k/λ) log(1/δ) such that with probability at least 1 − δ, for any w_i, i ∈ [k], with
β_i ≥ λ, there exists a vector r_i ∈ L such that |r_i · w_i| ≥ 0.99."

**Formalization Note.**
* The algorithm is one program `P` of the published sampling real RAM `GaussMixHH`, restricted by
  `SelfSelReg.ArithmeticCoin` to exact `+ − × ÷`, rational literals, comparisons, memory and pointer
  moves, a pointer-to-real cast, fair coins, `sample` and `halt` (no `√`, `exp`, `cos`, `sin`, no
  eigensolver). `P` and `C` are chosen before every parameter and instance. `P` runs in dimension
  `d + 1`, reads `k, λ, δ` from memory (`cdrInput`) and reaches `D` only through `sample` (one
  example `(x, f(x))` per call, cost `d + 1`). Work counts executed instructions.
* `poly(·)`: `N = C(d + k + 1/λ + 1/δ)^C` bounds the samples, `C(d + N)^C` the work, and
  `C(k/λ)^C(1 + log(1/δ))` the list length, on **every** coin tape and sample stream.
* **Correction.** The printed `|L| = poly(k/λ) log(1/δ)` is false for `δ` near `1`: for any
  constants `c, C'`, take `d = k = 1`, `w₁ = 1`, `β₁ = 1`, `λ = 1/2` and `δ < 1` so close to
  `1` that `C'(k/λ)^c log(1/δ) < 1`; then `L = ∅`, yet the guarantee for `i = 1` must hold with
  probability `1 − δ > 0`. The bound `C(k/λ)^C(1 + log(1/δ))` is the minimal repair (the proof's
  list has `2N_u`, `N_u = poly(k/λ) log(k/δ)`, elements, p.48).
* The output list is `r_j = rawVec_j/‖rawVec_j‖`, `j < listLength`, read from memory
  (`cdrOutput`); exact unit vectors need `√`, so the raw vectors are normalized by the decoder and
  are required nonzero. Natural logarithm. -/
theorem proposition_4_1 :
    ∃ (P : GaussMixHH.Program) (_ : GaussMixHH.Admissible P) (_ : SelfSelReg.ArithmeticCoin P)
      (C : ℕ),
      ∀ (d k : ℕ), 1 ≤ d → 1 ≤ k → ∀ (lam δ : ℝ), 0 < lam → lam < 1 → 0 < δ → δ < 1 →
      ∀ (β : Fin k → ℝ) (w : Fin k → EuclideanSpace ℝ (Fin d)), InClass β w →
        (∀ ω : (ℕ → Bool) × (ℕ → EuclideanSpace ℝ (Fin (d + 1))), ∃ t : ℕ,
          let s := GaussMixHH.run P (d + 1) (GaussMixHH.initState (d + 1) (cdrInput k lam δ)) ω t
          s.halted = true ∧
            (s.samplesUsed : ℝ) ≤ cdrSampleBound C d k lam δ ∧
            (s.work : ℝ) ≤ (C : ℝ) * ((d : ℝ) + cdrSampleBound C d k lam δ) ^ C ∧
            (listLength s : ℝ) ≤ (C : ℝ) * ((k : ℝ) / lam) ^ C * (1 + Real.log (1 / δ)) ∧
            ∀ j < listLength s, rawVec d s j ≠ 0) ∧
        ∃ E : Set ((ℕ → Bool) × (ℕ → EuclideanSpace ℝ (Fin (d + 1)))), MeasurableSet E ∧
          ENNReal.ofReal (1 - δ) ≤ sampleSpace β w E ∧
          ∀ ω ∈ E, ∀ t : ℕ,
            let s := GaussMixHH.run P (d + 1) (GaussMixHH.initState (d + 1) (cdrInput k lam δ)) ω t
            s.halted = true →
              ∀ i, lam ≤ β i → ∃ j < listLength s,
                (0.99 : ℝ) ≤ |inner ℝ (normalize (rawVec d s j)) (w i)| := by sorry

end SumReLU
