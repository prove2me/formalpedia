-- Prove2me | Theorems.Thm_QuantumKtSoI_Supplement_theorem_A_1
-- name    : QuantumKtSoI.Supplement.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:49:55.753469+00:00
-- url     : https://prove2.me/theorems/95d3efce-697a-41bf-b9c1-6c47a273abdf
-- title:
--   Theorem A.1, p.131 — an almost-determined classical sampler with $\Pr[\mathrm{qKt}(y|x)\le C\log n]=o(1)$ gives a quantum-secure one-way function
-- statement:
--   Let $S$ be a fixed classical polynomial-time sampler that, on $1^n$, outputs $(x,y)\in\{0,1\}^{m(n)}\times\{0,1\}^{m(n)}$, where $m$ is a fixed polynomially bounded, polynomial-time computable length function. Suppose that there are a constant $\delta_0>0$ and functions $\varphi_n:\{0,1\}^{m(n)}\to\{0,1\}^{m(n)}$ such that, for all sufficiently large $n$,
--   $$\Pr_x\Big[\Pr[y=\varphi_n(x)\mid x]\ge\tfrac{255}{256}\Big]\ge\delta_0,\tag{26}$$
--   where $x$ is the first coordinate of $S(1^n)$ and the inner probability is over the second coordinate given the first, and that for every constant $C>0$,
--   $$\Pr_{(x,y)\sim S(1^n)}[\mathrm{qKt}(y|x)\le C\log n]=o(1).\tag{27}$$
--   Then a quantum-secure classical one-way function (Definition 8.1) exists. No efficient evaluation of $\varphi_n$ is assumed.
--
--   This is the converse direction to Theorem 8.3: strong classical-sampling incompressibility implies one-wayness.
--
--   **Formalization Note** $o(1)$ is: for every $\varepsilon>0$, eventually at most $\varepsilon$.
--
--   Differences from the source:
--   - generalization: the glue routines are fixed once and for all by their p.24 properties → every admissible glue routine set G (hypothesis G.Admissible); descriptions, P_e and qKt are those of G; reason: the proofs use only the p.24 properties and the paper's routines are one admissible set; same as the published base items
--   - reading: a classical polynomial-time sampler with outputs in {0,1}^{m(n)} × {0,1}^{m(n)} → GSampler m: a §2.1 probabilistic Turing machine with an all-branch polynomial deadline and 2m(n) output bits on 1ⁿ; reason: the base mission's reading of classical samplers with output length 2m(n) in place of 2n
--   - reading: m polynomially bounded and polynomial-time computable → m(n) ≤ c(n+2)^k, and m computable on input b(n) in time polynomial in n; reason: no input format is named; the sampler receives 1ⁿ, so time polynomial in n is meant
--   - encoding: Pr_x[Pr[y = φ_n(x) | x] ≥ 255/256] ≥ δ₀ → the sum of Pr[X = x] over x with Pr[X = x] > 0 and Pr[X = x, Y = φ_n(x)] ≥ (255/256)·Pr[X = x] is at least δ₀; reason: a conditional probability is defined on x of positive probability
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem A.1, p.131; Definition 8.1, p.111

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt
import Definitions.Def_QuantumKtSoI_Supplement_GSampler
import Definitions.Def_QuantumKtSoI_Supplement_PolyInValue
import Definitions.Def_QuantumKtSoI_Supplement_QSOWF

open Classical

namespace QuantumKtSoI.Supplement

/-- **Theorem A.1** (Almost-determined classical sampling implies one-wayness; Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…, p.131). Let `S`
be a fixed classical polynomial-time sampler that, on `1ⁿ`, outputs `(x, y) ∈ {0,1}^{m(n)} ×
{0,1}^{m(n)}`, where `m` is a fixed polynomially bounded, polynomial-time computable length
function. Suppose that there are a constant `δ₀ > 0` and functions
`φ_n : {0,1}^{m(n)} → {0,1}^{m(n)}` such that, for all sufficiently large `n`,
(26) `Pr_x[Pr[y = φ_n(x) | x] ≥ 255/256] ≥ δ₀` (`x` the first coordinate of `S(1ⁿ)`, the inner
probability over the second coordinate given the first), and that for every constant `C > 0`,
(27) `Pr_{(x,y)∼S(1ⁿ)}[qKt(y|x) ≤ C log n] = o(1)`. Then a quantum-secure classical one-way function
(Definition 8.1) exists. No efficient evaluation of `φ_n` is assumed.

**Formalization Note** `S` is a `GSampler m` (§2.1 probabilistic Turing machine, all-branch
polynomial deadline, output `xy` of length `2m(n)`). In (26), `Pr_x[E(x)]` is the sum of
`Pr[X = x]` over the `x ∈ {0,1}^{m(n)}` with `Pr[X = x] > 0` and `E(x)`, and
`Pr[y = φ_n(x) | x] ≥ 255/256` is `Pr[X = x, Y = φ_n(x)] ≥ (255/256) Pr[X = x]`. `o(1)` is: for every
`ε > 0`, eventually at most `ε`. "Polynomially bounded" is `m(n) ≤ c(n+2)^k`; "polynomial-time
computable" is `PolyInValue m` (on input `b(n)`, time polynomial in `n`). `G` is any admissible glue
routine set (p.24); the conclusion does not involve `G`. -/
theorem theorem_A_1 (G : GlueRoutines) (hG : G.Admissible) (m : ℕ → ℕ)
    (hmb : ∃ c k : ℕ, ∀ n, m n ≤ c * (n + 2) ^ k) (hmc : PolyInValue m) (S : GSampler m)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (φ : ℕ → List Bool → List Bool)
    (hφ : ∀ n : ℕ, ∀ x : List Bool, x.length = m n → (φ n x).length = m n)
    (h26 : ∃ n₀ : ℕ, ∀ n ≥ n₀, δ₀ ≤ ∑ x : Fin (m n) → Bool,
      if 0 < S.prob n (fun X _ => X = List.ofFn x) ∧
          (255 / 256 : ℝ) * S.prob n (fun X _ => X = List.ofFn x) ≤
            S.prob n (fun X Y => X = List.ofFn x ∧ Y = φ n (List.ofFn x))
        then S.prob n (fun X _ => X = List.ofFn x) else 0)
    (h27 : ∀ C : ℝ, 0 < C → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      S.prob n (fun x y => (qKt G y x : ℝ) ≤ C * Real.logb 2 n) ≤ ε) :
    ∃ f : List Bool → List Bool, QuantumSecureOWF f := by sorry

end QuantumKtSoI.Supplement
