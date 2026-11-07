-- Prove2me | Theorems.Thm_ShadowBootstrap_theorem_7_1
-- name    : ShadowBootstrap.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:27:15.787495+00:00
-- url     : https://prove2.me/theorems/b8c262e0-87de-4414-a77b-7f762a77497f
-- title:
--   Theorem 7.1 — Algorithms 1 and 4: $\Pr[1 - |\langle\psi|\hat\psi\rangle|^2 \le \epsilon] \ge 5/6$, $T = O(d/\epsilon)$, $N = O(n^3 + \log(2/\epsilon))$, $\tilde O(d\log(2/\epsilon))$ time
-- statement:
--   There are integers $K_0, C_0$ such that for all integers $K \ge K_0$ (Algorithm 1's "sufficiently large constant") and $C \ge C_0$ (the constant of Algorithm 1, line 12) there are a constant $D$ and a map writing every label of the suffix ensembles $E_\ell$ of Lemma A.2 as a valid circuit over $\{H, S, CX\}$ of depth at most $D(\lfloor\log_2 n\rfloor + 1)$ realizing its unitary up to a global phase, such that for every $n$ and $\epsilon \in (0,1)$, with $d = 2^n$:
--
--   1. the schedule of Algorithm 1 has $T \le D\,d/\epsilon$ copies and $N \le D\,(n^3 + \log(2/\epsilon))$ settings, for every sampled label;
--   2. for every rule choosing normalized top eigenvectors in Algorithm 3, the output $|\hat\psi\rangle$ of Algorithms 3–4 is a unit vector on every histogram data, and for every unit vector $|\psi\rangle$,
--   $$\Pr\big[1 - |\langle\psi|\hat\psi\rangle|^2 \le \epsilon\big] \ge \tfrac56;$$
--   3. there are an eigenvector rule and one real-RAM program (rational literals, no randomness) that, given $\epsilon$, the encoded schedule and the histograms, halts within $D\,d\log(2/\epsilon)\,L^D$ steps and writes at most $D\,d\,L^D$ cells, with $L = 1 + n + \log(1/\epsilon)$, and outputs exactly the vector of Algorithms 3–4, on every histogram data.
--
--   The measurements are nonadaptive and single-copy; the classical post-processing reads only per-basis histograms.
--
--   Differences from the source:
--   - reading: Algorithm 1 with a sufficiently large constant K and the constant C of Corollary 4.5 → every pair of integers K ≥ K₀, C ≥ C₀; the bound constant D may depend on them; reason: the copy count grows linearly in K and C, so D must
--   - reading: Clifford measurements of depth O(log n) → a circuit map for the ensembles' labels into valid {H, S, CX} circuits of depth ≤ D(⌊log₂ n⌋ + 1), equal up to a global phase; reason: the gate set and depth notion of §3.1 and Lemma 6.1
--   - reading: Õ(d log(2/ϵ)) time and Õ(d) working memory → a real-RAM program halting within D·d·log(2/ϵ)·L^D steps and writing ≤ D·d·L^D distinct cells, L = 1 + n + log(1/ϵ); reason: p.4: Õ suppresses polylogarithmic factors in d and 1/ϵ; the paper counts arithmetic operations including √
--   - generalization: Algorithms 1 and 4 output ψ̂ with the success probability → for every eigenvector rule; output a unit vector on every histogram data; n = 0 included; reason: Algorithm 3, line 9 allows any normalized top eigenvector; the bounds also hold at n = 0
--   - encoding: per-basis outcome histograms → dense count arrays in index order, after ϵ in the real cells; settings encoded in the index cells; reason: the same data
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), Theorem 7.1 and its proof, pp.27–28; Algorithms 1–4, pp.26–27

import Mathlib
import Definitions.Def_ShadowBootstrap_alg1Data

open ClassicalShadow.Linear ShallowShadows.ShadowNorm

namespace ShadowBootstrap

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Theorem 7.1, pp.27–28 (full algorithm at constant confidence): for any `n`-qubit pure state `|ψ⟩`
and `ϵ ∈ (0, 1)`, Algorithms 1 and 4 output a unit vector `|ψ̂⟩` with
`Pr[1 − |⟨ψ|ψ̂⟩|² ≤ ϵ] ≥ 5/6`. The protocol uses nonadaptive single-copy Clifford measurements of
depth `O(log n)`, with `T = O(d/ϵ)` and `N = O(n³ + log(2/ϵ))`. Given per-basis outcome histograms,
classical post-processing takes `Õ(d log(2/ϵ))` time and `Õ(d)` working memory.

**Formalization Note** Algorithm 1's "sufficiently large constant `K`" and the constant `C` of its
line 12 are integers `K ≥ K₀`, `C ≥ C₀`; every bound constant `D` may depend on them. The schedule
is Algorithm 1 (`alg1Data`) with the ensembles of Lemma A.2 (`E_ℓ` at level `ℓ`, `E = E_0` at the
stages), every sampled label written as a valid `{H, S, CX}` circuit (`circ`) realizing its
unitary up to a global phase. `T` and `N` are the total shots and the number of settings of that
schedule (with multiplicity), for every sampled label. The success probability (`alg1SuccessProb`)
is over the labels and the outcomes, for **every** eigenvector rule of Algorithm 3 (line 9), and
the output of Algorithms 3–4 (`postprocess`) is a unit vector on every histogram data. The time and
memory clause: one real-RAM program with rational literals and no randomness, reading `ϵ`, the
encoded schedule and the dense histograms (`encodeData`), halts within
`D·d·log(2/ϵ)·L^D` steps with `L = 1 + n + log(1/ϵ)` (`Õ` suppresses polylogarithmic factors in `d`
and `1/ϵ`, p.4), writes at most `D·d·L^D` cells, and outputs exactly Algorithm 3–4's vector for one
eigenvector rule, on every histogram data. `n = 0` is included. -/
theorem theorem_7_1 :
    ∃ K₀ C₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ C : ℕ, C₀ ≤ C → ∃ D : ℝ,
      ∀ [∀ k, Fintype (CliffordLabel k)],
      ∃ circ : (n j : ℕ) → SuffixLabel n j → Circuit j,
        (∀ n j : ℕ, j ≤ n → ∀ lab : SuffixLabel n j,
          Circuit.IsValid (circ n j lab) ∧
          (depth (circ n j lab) : ℝ) ≤ D * (Nat.log 2 n + 1) ∧
          ∃ c : ℂ, ‖c‖ = 1 ∧ circUnitary (circ n j lab) = c • (suffixEnsemble n j).mat lab) ∧
        (∀ (n : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
          ∀ (initL : (j : Fin n) → Fin (initN K n) → SuffixLabel n (j.1 + 1))
            (initC : (j : Fin n) → Fin (initN K n) → Bits n → ℕ)
            (refL : Fin (refJ ε) → Fin (refN C) → SuffixLabel n n)
            (refC : Fin (refJ ε) → Fin (refN C) → Bits n → ℕ),
          ((totalShots ((alg1Data circ K C n ε initL initC refL refC).map Prod.fst) : ℕ) : ℝ)
              ≤ D * 2 ^ n / ε ∧
          (((alg1Data circ K C n ε initL initC refL refC).length : ℕ) : ℝ)
              ≤ D * ((n : ℝ) ^ 3 + Real.log (2 / ε))) ∧
        (∀ choose : Matrix (Fin 2) (Fin 2) ℂ → Fin 2 → ℂ, IsTopEigRule choose →
          ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
            (∀ (initL : (j : Fin n) → Fin (initN K n) → SuffixLabel n (j.1 + 1))
              (initC : (j : Fin n) → Fin (initN K n) → Bits n → ℕ)
              (refL : Fin (refJ ε) → Fin (refN C) → SuffixLabel n n)
              (refC : Fin (refJ ε) → Fin (refN C) → Bits n → ℕ),
              IsUnitVec (postprocess choose K C n ε initL initC refL refC)) ∧
            ∀ ψ : Bits n → ℂ, IsUnitVec ψ → 5 / 6 ≤ alg1SuccessProb choose K C n ε ψ) ∧
        ∃ choose : Matrix (Fin 2) (Fin 2) ℂ → Fin 2 → ℂ, IsTopEigRule choose ∧
        ∃ P : MatMulTimeLP.Program, RationalLiterals P ∧ NoRandom P ∧
          ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
          ∀ (initL : (j : Fin n) → Fin (initN K n) → SuffixLabel n (j.1 + 1))
            (initC : (j : Fin n) → Fin (initN K n) → Bits n → ℕ)
            (refL : Fin (refJ ε) → Fin (refN C) → SuffixLabel n n)
            (refC : Fin (refJ ε) → Fin (refN C) → Bits n → ℕ),
            HaltsWithin P (encodeData [ε] (alg1Data circ K C n ε initL initC refL refC))
                (D * 2 ^ n * Real.log (2 / ε) * (1 + n + Real.log (1 / ε)) ^ D) ∧
            (cellsWritten P (encodeData [ε] (alg1Data circ K C n ε initL initC refL refC)) : ℝ)
                ≤ D * 2 ^ n * (1 + n + Real.log (1 / ε)) ^ D ∧
            dataOutput P [ε] (alg1Data circ K C n ε initL initC refL refC) =
              postprocess choose K C n ε initL initC refL refC := by sorry

end ShadowBootstrap
