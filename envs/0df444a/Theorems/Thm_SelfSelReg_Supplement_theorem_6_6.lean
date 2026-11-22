-- Prove2me | Theorems.Thm_SelfSelReg_Supplement_theorem_6_6
-- name    : SelfSelReg.Supplement.theorem_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T05:20:17.940804+00:00
-- url     : https://prove2.me/theorems/91d6d9a3-e401-4f7d-9b58-535bdd29dc56
-- title:
--   Theorem 6.6 — normalized-regressor recovery
-- statement:
--   Let $K=16(1+B^2)^3/\Delta^4$ with $B\ge1$, $\Delta\in(0,1]$, and let $2\le k\le n$. Let $J\subseteq[k]$ have $p\ge2$ elements, and suppose the vectors $(a_i)_{i\in J}$ in $\mathbb R^n$ satisfy
--
--   $$
--   K^{-3}\le\|a_i\|_2\le K^3\quad(i\in J),\qquad\|a_i-a_{i'}\|_2\ge K^{-3}\quad(i\ne i').
--   $$
--
--   Fix $\varepsilon_{\mathrm{fam}}\ge0$ and suppose the symmetric matrices $\widehat D_1,\dots,\widehat D_n\in\mathbb R^{p\times p}$ form an $\varepsilon_{\mathrm{fam}}$-approximate observable-operator family for $(a_i)_{i\in J}$ (Definition 6.4). Given these matrices and $\delta\in(0,1/3)$, RECOVERDIRECTIONS (Algorithm 6.3) returns unit vectors $\widehat u_1,\dots,\widehat u_p$ such that, with probability at least $1-\delta$, there is a bijection $\pi:[p]\to J$ with
--
--   $$
--   \max_{i\in[p]}\Bigl\|\widehat u_i-\frac{a_{\pi(i)}}{\|a_{\pi(i)}\|_2}\Bigr\|_2\le32K^6\sqrt n\,p^2\,\varepsilon_{\mathrm{fam}}.
--   $$
--
--   Moreover, the routine runs in time $\mathrm{poly}(n,k)\log(1/\delta)$.
--
--   The theorem is the decoding step: random contractions of the family have well-separated eigenvalues with constant probability, and their eigenvectors then give every coordinate of every $a_i$ with the same labelling.
--
--   **Formalization Note** The statement has two parts. (1) Correctness: the directions $b_1,b_2,\dots$ are independent and uniform on the unit sphere; every output of Algorithm 6.3 consists of unit vectors, and on an event of probability at least $1-\delta$ every output (every choice of eigenvectors and of the maximizing trial) admits a bijection with the displayed bound. (2) Running time: there are one program and one constant $C$ such that, on all symmetric inputs with $2\le p\le k$ and all $L=\lceil\log_2(1/\delta)\rceil$ drawn directions, the program halts within $C(n+k)^C\log(1/\delta)$ units of work with an output of Algorithm 6.3 for those directions. The program runs on the published unit-cost real RAM with square roots and a symmetric eigensolver charged $d^3+1$ on a $d\times d$ matrix.
--
--   Differences from the source:
--
--   - encoding: RECOVERDIRECTIONS (Algorithm 6.3) returns unit vectors such that, with probability at least 1 − δ, … → the directions are an i.i.d. sequence with the uniform law on the sphere (the law of G/‖G‖₂, G standard Gaussian); there is a measurable event of probability at least 1 − δ on which every pair in the input–output relation of Algorithm 6.3 (any orthonormal eigenvectors, any maximizing trial) satisfies the bound; reason: the pseudocode fixes neither the eigenvectors nor the tie-break; the probability is over the drawn directions only
--   - reading: L ← log₂(1/δ) → L = ⌈log₂(1/δ)⌉; reason: L counts trials and the proof uses 2^{−L} ≤ δ
--   - reading: û_i ← â_i/‖â_i‖₂ and "returns unit vectors", with no rule for â_i = 0 → when â_i = 0 the output û_i may be any unit vector; reason: the hypotheses allow â_i = 0 (for ε_fam ≥ K³√p the zero matrices are an ε_fam-approximate family); a quotient 0/0 is not a unit vector, and the paper shows â_i ≠ 0 only when ε_fam is small (after (81))
--   - reading: "the routine runs in time poly(n, k) log(1/δ)", no machine named; the proof counts each eigendecomposition as a polynomial-time step and line 2 draws real vectors → one program of the published unit-cost real RAM with √ and a charged exact symmetric eigensolver (cost d³ + 1), and one constant C, such that on all symmetric inputs with 2 ≤ p ≤ k, given the L drawn directions in its input, it halts within C(n + k)^C·log(1/δ) work with an output of Algorithm 6.3 for those directions; reason: the bound (44) is exact at ε_fam = 0, and exact eigenvectors are not computable from + − × ÷ √ and comparisons, so the arithmetic-only machine of the published goal cannot return an output of Algorithm 6.3; the published machine has no instruction drawing a real vector, so the draws are inputs and reading them is charged
--   - encoding: K, and J ⊆ [k] with vectors in ℝⁿ → K = 16(1 + B²)³/∆⁴ for B ≥ 1, ∆ ∈ (0, 1] (the published hypK), with 2 ≤ k ≤ n; reason: K is the constant of Hyperparameters 4.1 throughout the paper and 2 ≤ k ≤ n is the range of Definition 1.1
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Theorem 6.6, p.31 (PDF p.34); Algorithm 6.3, p.43 (PDF p.46)

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_Machine
import Definitions.Def_SelfSelReg_hypK
import Definitions.Def_SelfSelReg_Supplement_Routine
import Definitions.Def_SelfSelReg_Supplement_ObservableFamily
import Definitions.Def_SelfSelReg_Supplement_EigDecomp
import Definitions.Def_SelfSelReg_Supplement_RecoverDirections

open MeasureTheory ProbabilityTheory

namespace SelfSelReg

namespace Supplement

/-- **Theorem 6.6** (Normalized-Regressor Recovery).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Theorem 6.6, p.31 (PDF p.34); Algorithm 6.3, p.43 (PDF p.46):
"Let J ⊆ [k] have p ≥ 2 elements, and suppose the vectors (a_i)_{i∈J} in ℝⁿ satisfy
K^{−3} ≤ ‖a_i‖₂ ≤ K³ (i ∈ J), ‖a_i − a_{i′}‖₂ ≥ K^{−3} (i ≠ i′). Fix ε_fam ≥ 0. Suppose the symmetric
matrices D̂_1, …, D̂_n ∈ ℝ^{p×p} form an ε_fam-approximate observable-operator family for (a_i)_{i∈J}
(Definition 6.4). Given these matrices and δ ∈ (0, 1/3), RECOVERDIRECTIONS (Algorithm 6.3) returns unit
vectors û_1, …, û_p such that, with probability at least 1 − δ, there is a bijection π : [p] → J
satisfying max_{i∈[p]} ‖û_i − a_{π(i)}/‖a_{π(i)}‖₂‖₂ ≤ 32K⁶√n p² ε_fam (44). Moreover, the routine runs in
time poly(n, k) log(1/δ)."

The statement has two parts.

1. **Correctness.** For arbitrary vectors `(a_i)_{i∈J}` and matrices `D̂` as in the hypotheses: every
   output of Algorithm 6.3 consists of unit vectors, and there is an event of probability at least
   `1 − δ` for the independent uniform directions `b_1, b_2, …` on which **every** output `û` of
   Algorithm 6.3 (`IsRecoverOutput`: every choice of eigenvectors and of the maximizing trial) admits a
   bijection `π : [p] → J` with the bound (44).
2. **Running time.** One program `P` and one constant `C`: on all symmetric inputs
   `D̂_1, …, D̂_n ∈ ℝ^{p×p}` with `2 ≤ p ≤ k`, every `δ ∈ (0, 1/3)` and every list of `L = ⌈log₂(1/δ)⌉`
   drawn directions, `P` halts within `C (n + k)^C log(1/δ)` units of work and its output is an output
   of Algorithm 6.3 for those directions.

**Formalization Note.**
* `K` is the published `hypK B ∆` of Hyperparameters 4.1 with `B ≥ 1`, `∆ ∈ (0, 1]`, and `2 ≤ k ≤ n`
  as in Definition 1.1; the vectors `a_i` are arbitrary (not tied to the model).
* `Unif(S^{n−1})` is `sphereLaw n`; the directions are an i.i.d. sequence with that law, of which the
  routine uses the first `L` (`numTrials δ`).
* The running time is counted as the paper counts it, with each eigendecomposition as a
  polynomial-time step ("Each of the L = O(log(1/δ)) trials forms a p × p matrix and computes its
  eigendecomposition. Since p ≤ k, these computations and the coordinate quadratic forms take
  poly(n, k) log(1/δ) time", p.46, PDF p.49): `P` is a program of the published unit-cost real RAM
  with a charged exact symmetric eigensolver, `ExpanderWalkDecode.Main` (`eig` on a `d × d` matrix
  costs `d³ + 1`; `√` is an instruction). Exact eigenvectors are not computable from `+ − × ÷ √` and
  comparisons, and the bound (44) is exact when `ε_fam = 0`, so no program without such a step
  returns an output of Algorithm 6.3. That machine has no instruction drawing a real vector: the `L`
  drawn directions of line 2 are supplied in the input, and reading them is charged.
* Input: real bank `0` holds `δ`, then `D̂_1, …, D̂_n` row by row, then `b_1, …, b_L`; integer bank `0`
  holds `n, p`. Output list: `û_1, …, û_p`, coordinate by coordinate. Given the directions the routine
  is deterministic: `RunsWithin … 1` asks for a correct output on every coin tape. -/
theorem theorem_6_6 :
    (∀ (n k p : ℕ), 2 ≤ k → k ≤ n → 2 ≤ p →
      ∀ (B Δ : ℝ), 1 ≤ B → 0 < Δ → Δ ≤ 1 →
      ∀ (a : Fin k → EuclideanSpace ℝ (Fin n)) (J : Finset (Fin k)) (hJ : J.card = p),
        (∀ i ∈ J, 1 / hypK B Δ ^ 3 ≤ ‖a i‖ ∧ ‖a i‖ ≤ hypK B Δ ^ 3) →
        (∀ i ∈ J, ∀ i' ∈ J, i ≠ i' → 1 / hypK B Δ ^ 3 ≤ ‖a i - a i'‖) →
      ∀ εfam : ℝ, 0 ≤ εfam →
      ∀ D : Fin n → Matrix (Fin p) (Fin p) ℝ, IsApproxObservableFamily a J hJ D εfam →
      ∀ δ : ℝ, 0 < δ → δ < 1 / 3 →
        (∀ (b : ℕ → EuclideanSpace ℝ (Fin n)) (u : Fin p → EuclideanSpace ℝ (Fin n)),
          IsRecoverOutput D δ b u → ∀ i, ‖u i‖ = 1) ∧
        ∃ Ev : Set (ℕ → EuclideanSpace ℝ (Fin n)), MeasurableSet Ev ∧
          ENNReal.ofReal (1 - δ) ≤ (Measure.infinitePi fun _ : ℕ => sphereLaw n) Ev ∧
          ∀ b ∈ Ev, ∀ u : Fin p → EuclideanSpace ℝ (Fin n), IsRecoverOutput D δ b u →
            ∃ π : Fin p ≃ {i : Fin k // i ∈ J},
              ∀ i, ‖u i - ‖a (π i)‖⁻¹ • a (π i)‖ ≤
                32 * hypK B Δ ^ 6 * Real.sqrt n * (p : ℝ) ^ 2 * εfam) ∧
    ∃ (P : ExpanderWalkDecode.Main.Program) (_ : ExpanderWalkDecode.Main.Admissible P) (C : ℕ),
      ∀ (n k p : ℕ), 1 ≤ n → 2 ≤ p → p ≤ k →
      ∀ δ : ℝ, 0 < δ → δ < 1 / 3 →
      ∀ D : Fin n → Matrix (Fin p) (Fin p) ℝ, (∀ l, (D l).IsHermitian) →
      ∀ b : ℕ → EuclideanSpace ℝ (Fin n),
        ExpanderWalkDecode.Main.RunsWithin P
          (ExpanderWalkDecode.Main.init
            (fun bank => if bank = 0 then
                ExpanderWalkDecode.Main.listBank
                  ([δ] ++ (List.ofFn fun l => matData (D l)).flatten ++
                    (List.ofFn fun ι : Fin (numTrials δ) => vecData (b ι)).flatten)
              else fun _ => 0)
            (fun bank => if bank = 0 then ExpanderWalkDecode.Main.listIBank [(n : ℤ), (p : ℤ)]
              else fun _ => 0))
          (C * ((n : ℝ) + k) ^ C * Real.log (1 / δ))
          (fun out => ∃ u : Fin p → EuclideanSpace ℝ (Fin n),
            out = (List.ofFn fun i => vecData (u i)).flatten ∧ IsRecoverOutput D δ b u)
          1 := by sorry

end Supplement

end SelfSelReg
