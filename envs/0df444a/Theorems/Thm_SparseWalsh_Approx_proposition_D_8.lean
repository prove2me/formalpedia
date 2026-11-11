-- Prove2me | Theorems.Thm_SparseWalsh_Approx_proposition_D_8
-- name    : SparseWalsh.Approx.proposition_D_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:04:17.916186+00:00
-- url     : https://prove2.me/theorems/80bb62f7-b64e-4498-89c6-9312b182ca55
-- title:
--   Proposition D.8 — Algorithm 3 meets the four running-time bounds of Theorem 5.1 on every execution
-- statement:
--   Proposition D.8 states: "Algorithm 3 satisfies the four running-time bounds in Theorem 5.1 on every execution."
--
--   Formally, there are a code family meeting the interface of Lemma D.7, an admissible program $P$ of the machine of §2 and a universal constant $C$ with the following properties. The code family is injective, has rate at most $c_0$, and corrects every pattern of at most $\beta P$ errors, $0<\beta\le1/8$. Put $\Lambda=\log_2(4ds/\varepsilon)$. Take any $d\ge1$, $1\le s\le2^d$, $0<\varepsilon\le1$, either method, either output limit, and either setting: the general one ($L=d$), or the degree setting with $1\le k\le d$ ($L=k\log_2(2d/k)$). Then there is a map from coin tapes to "timeout" or to an outcome of Algorithm 3's random objects, fixed before $f$, such that:
--   - each outcome has probability at most its probability under Algorithm 3's law;
--   - a timeout has probability at most $1/16$;
--   - for every $f$ and every tape, the run halts with work at most $C\,T_{\rm row}\,\Lambda^C$, where $T_{\rm row}$ is $ds/\varepsilon^2$, $ds/\varepsilon$, $dLs/\varepsilon+ds/\varepsilon^2$ or $dLs/\varepsilon$ for the four rows of (7);
--   - the run aborts exactly on a timeout, and otherwise lists Algorithm 3's output on the sampled objects, each frequency once with its coefficient.
--
--   This is the running-time half of Theorem 5.1. It includes setup, sampling with the setup-time limit of §2, query preparation, reconstruction and writing the output.
--
--   Differences from the source:
--
--   - reading: Algorithm 3 satisfies the running-time bounds on every execution → there is a program that implements Algorithm 3: a map from tapes to its random objects or a timeout, fixed before f, with law at most randLaw on each outcome and timeout probability at most 1/16, such that every run halts within C·T_row·Λ^C, aborts exactly on a timeout and otherwise outputs algorithm3 on the sampled objects; reason: "execution of Algorithm 3" under the setup-time convention of §2 (timeouts are part of every execution, Lemma A.1 bounds them by 1/16); without the law and timeout clauses a program that always aborts would meet the time bound
--   - encoding: Õ(·) suppressing logarithmic factors in d, s, 1/ε; one implementation per row → C·T_row·Λ^C with Λ = log₂(4ds/ε) and one universal C, one program with the method and output flags as inputs; reason: Λ ≥ 2 and every logarithmic factor in d, s, 1/ε is at most a power of Λ
--   - encoding: Algorithm 3's code (Lemma D.7) → an existentially chosen code family meeting the interface of Lemma D.7 (injective, rate ≤ c₀, corrects βP errors, 0 < β ≤ 1/8); reason: the running time depends on the code's implementation, which the program supplies
--   - generalization: inputs of Theorem 5.1 (degree promise in the degree setting) → every f : F_2^d → ℝ, with or without the promise; reason: the running time does not depend on the promise; the statement specializes to promised inputs
--   - reading: L = O(k log(2d/k)) → L = k·log₂(2d/k); reason: the O-constant is absorbed into C
-- source:
--   Attias, Bshouty, Medvedev, Srebro, Efficient Non-Adaptive Sparse Fourier Learning on the Boolean Cube and Finite Abelian Groups, STOC 2027 submission (manuscript sha256 4cbf9075…), p. 48 (PDF p. 51), Proposition D.8; proof pp. 48-50, App. D.7.2

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_SparseWalsh_Approx_Fourier
import Definitions.Def_SparseWalsh_Approx_Locators
import Definitions.Def_SparseWalsh_Approx_Algorithm3
import Definitions.Def_SparseWalsh_Approx_Machine

open scoped BigOperators Matrix

namespace SparseWalsh.Approx

/-- **Proposition D.8** (Running time for approximation), p. 48 (PDF p. 51): "Algorithm 3
satisfies the four running-time bounds in Theorem 5.1 on every execution."

Reading. There are a code family meeting the interface of Lemma D.7 (injective, rate `≤ c₀`,
correcting every pattern of at most `βP` errors, `0 < β ≤ 1/8`), one admissible program `P` of the
machine and one universal constant `C` such that for every `1 ≤ s ≤ 2^d`, `ε ∈ (0, 1]`, method,
output limit and setting (`k = 0`: `L = d`; `1 ≤ k ≤ d`: `L = k·log₂(2d/k)`), `P` implements
Algorithm 3 with that code family under the setup-time convention of §2: there is a map `sample`
from coin tapes to the random objects of Algorithm 3 or to "timeout", fixed before `f`, whose law
on each outcome is at most Algorithm 3's law (`randLaw`) and which times out with probability at
most `1/16`; and for every `f` and every tape the run halts with `work ≤ C·T_row·Λ^C`
(`Λ = log₂(4ds/ε)`, `T_row` as in Theorem 5.1), aborts exactly on a timeout, and otherwise
outputs Algorithm 3's result on the sampled objects (distinct frequencies, the output set and its
coefficients). -/
theorem proposition_D_8 :
    ∃ (c₀ β : ℝ) (codes : (D : ℕ) → BinCode D), 0 < c₀ ∧ 0 < β ∧ β ≤ 1 / 8 ∧
      (∀ D : ℕ, 1 ≤ D → Function.Injective (fun msg : Cube D => (codes D).E *ᵥ msg) ∧
        ((codes D).P : ℝ) ≤ c₀ * D ∧ (codes D).Corrects β) ∧
      ∃ (P : Program) (_ : Admissible P) (C : ℝ), 0 < C ∧
      ∀ d s : ℕ, 1 ≤ d → 1 ≤ s → s ≤ 2 ^ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ (coding twoS : Bool) (k : ℕ), (k = 0 ∨ (1 ≤ k ∧ k ≤ d)) →
        let meth : Method := if coding then .coding else .repetition
        let lim : OutLimit := if twoS then .double else .single
        let L : ℝ := if k = 0 then (d : ℝ) else k * Real.logb 2 (2 * d / k)
        let Λ : ℝ := Real.logb 2 (4 * d * s / ε)
        let Trow : ℝ :=
          if coding then (if twoS then d * L * s / ε else d * L * s / ε + d * s / ε ^ 2)
          else (if twoS then d * s / ε else d * s / ε ^ 2)
        let s₀ := approxInit d s ε coding twoS k
        ∃ sample : (ℕ → Bool) → Option (Rand β d s ε k meth lim),
          (∀ ρ : Rand β d s ε k meth lim,
            coinTape {ω | sample ω = some ρ} ≤ randLaw β d s ε k meth lim ρ) ∧
          coinTape {ω | sample ω = none} ≤ 1 / 16 ∧
          ∀ (f : Cube d → ℝ) (ω : ℕ → Bool), ∃ n : ℕ,
            (run P f s₀ ω n).halted = true ∧
            ((run P f s₀ ω n).work : ℝ) ≤ C * Trow * Λ ^ C ∧
            (sample ω = none → aborted (run P f s₀ ω n)) ∧
            ∀ ρ : Rand β d s ε k meth lim, sample ω = some ρ →
              ¬ aborted (run P f s₀ ω n) ∧
              ((outList (run P f s₀ ω n)).map Prod.fst).Nodup ∧
              ((outList (run P f s₀ ω n)).map Prod.fst).toFinset =
                (algorithm3 codes β d s ε k meth lim f ρ).1 ∧
              ∀ e ∈ outList (run P f s₀ ω n),
                e.2 = (algorithm3 codes β d s ε k meth lim f ρ).2 e.1 := by sorry

end SparseWalsh.Approx
