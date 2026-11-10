-- Prove2me | Theorems.Thm_RevRedSAT_lemma_A_2
-- name    : RevRedSAT.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:46:45.524134+00:00
-- url     : https://prove2.me/theorems/a7690ab0-bf99-4a90-a85c-9a7680d875bb
-- title:
--   Lemma A.2 — combining algorithms with rates $2^{\beta_jk+o_j(k)}$, $\beta_j\to0$, into one $2^{o(k)}$ algorithm
-- statement:
--   Consider a search problem with parameter $k$ and nonempty input codes $w$. Suppose that:
--
--   1. a common preprocessing maps $w$ to a word $\mathrm{pre}(w)$ in $P(I,w)$ steps;
--   2. a single procedure $U$ simulates $A_j$ from its index: on input $j$ followed by $\mathrm{pre}(w)$ it halts with a correct search output within $T_j(I,w)$ steps, where $T_j(I,w)\le 2^{\beta_jk+h_j(k)}|w|^{c}$ with $\beta_j\to0$, $h_j(k)/k\to0$ for each $j$, and $c$ independent of $j$;
--   3. a correct fallback runs within $f(k)|w|^{c_0}$ steps, $f$ computable;
--   4. $A_1,\dots,A_{\max\{1,k\}}$ can be simulated in round-robin, including initialization, with a fixed polynomial overhead in their total work: some machine solves the problem within $P(I,w)+\bigl((\max\{1,k\}+1)(\min\{T_1,\dots,T_{\max\{1,k\}}\}+1)\bigr)^{a}$ steps for a fixed $a$.
--
--   Then a single algorithm solves the problem within $P(I,w)+2^{g(k)}|w|^{c'}$ steps for some $c'$ and some $g$ with $g(k)/k\to0$.
--
--   **Formalization Note** Item 4 is the reading of "a fixed polynomial overhead in their total work". Codes are nonempty (§3, p.27).
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{o(·)}, 2^{O(·)} classes
--   - reading: an algorithm for the problem (Table 1: 'Det.; search') → a search algorithm: output 'no' exactly on NO-instances, otherwise the list of a feasible solution; reason: Table 1, App. C and the proofs (solution recovery) state search; the decision-only reading is weaker
--   - encoding: 2^{o(k)} → 2^{g(k)} for one g : ℕ → ℕ with g(k)/k → 0, chosen with the machine before the instance; reason: the definition of o(k); no rate of convergence is asked
--   - reading: A_1, …, A_{max{1,k}} can be simulated, including initialization, with a fixed polynomial overhead in their total work → a machine solves the problem within P(I, w) + ((max{1,k} + 1)·(min{T_1, …, T_{max{1,k}}} + 1))^a; reason: the total work of a round-robin run of the max{1,k} algorithms until the first answer is at most max{1,k} times the fastest running time (the factor max{1,k} + 1 leaves room for one more interleaved procedure); the overhead is a fixed power a; the fallback stays a separate hypothesis, as printed
--   - encoding: o_j(k) in the exponent of T_j → a function h_j with h_j(k)/k → 0 for each j; reason: the meaning of o_j(k)
--   - encoding: |I| and P(I, k) → |w| (codes assumed nonempty, §3) and P(I, w); reason: the input length is the length of the code
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma A.2, p.86 (printed) = PDF p.88

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_RevRedSAT_SearchWithin

set_option autoImplicit false

namespace RevRedSAT

open Filter Topology RSListDecodingCapacity.AllRates

/-- **Lemma A.2 (combining algorithms with decreasing exponential rates).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma A.2, p.86: "Suppose correct algorithms Aj, j ≥ 1, solve a parameter-k problem after
common preprocessing of cost P(I, k). A single procedure can simulate Aj from its index j. For every
fixed j, suppose its subsequent running time satisfies Tj(I, k) ≤ 2^{βj k+oj(k)}|I|^c with βj → 0,
where c is independent of j. Assume that A1, . . . , A_{max{1,k}} can be simulated, including
initialization, with a fixed polynomial overhead in their total work. If a correct fallback runs in
time f(k)|I|^{c0} for computable f and fixed c0, then a single algorithm solves the problem in time
P(I, k) + 2^{o(k)}|I|^{O(1)}."

Setting: a search problem with instances `I`, nonempty codes `w`, feasible solutions `valid I` and
parameter `κ(I) = k`.
* Preprocessing: the machine `Mpre` maps `w` to `pre w` within `P(I, w)` steps.
* Simulation from the index: one machine `U`, on input `j` followed by `pre w`, halts within
  `T_j(I, w)` steps with a correct search output, for every `j ≥ 1`; and
  `T_j(I, w) ≤ 2^{β_j k + h_j(k)}·|w|^c` with `β_j → 0`, `h_j(k)/k → 0` for each `j`, `c` fixed.
* Fallback: a machine `Mfb` solves the problem within `f(k)·|w|^{c₀}`, `f` computable.
* Simulation with a fixed polynomial overhead: some finite-alphabet machine solves the problem
  within `P(I, w) + ((max{1,k} + 1)·(min{T_1, …, T_{max{1,k}}} + 1))^a` steps for a fixed `a`.
Conclusion: a finite-alphabet machine solves the problem within `P(I, w) + 2^{g(k)}·|w|^{c'}` with
`g(k)/k → 0`.

**Formalization Note** The simulation hypothesis is read as: running the preprocessing once and
then `A_1, …, A_{max{1,k}}` in round-robin, until the first answer, costs at most a fixed power `a`
of the total work of the round-robin, `max{1,k}` algorithms times the time of the fastest one (the
factor `max{1,k} + 1` leaves room for one more interleaved procedure). The fallback is not part of
this hypothesis; it is the separate hypothesis `hfb`, as on the page. Codes are nonempty (§3, p.27: "assume that both encodings are nonempty"). -/
theorem lemma_A_2 {ι : Type} (n : ι → ℕ) (IsCode : ι → List Bool → Prop)
    (valid : (I : ι) → Finset (Fin (n I)) → Prop) (κ : ι → ℕ)
    (hne : ∀ I w, IsCode I w → w ≠ [])
    (P : ι → List Bool → ℕ) (Mpre : Turing.TM2ComputableAux Bool Bool) (pre : List Bool → List Bool)
    (hpre : ∀ I w, IsCode I w → HMBinPacking.OutputsWithin Mpre w (pre w) (P I w))
    (U : Turing.TM2ComputableAux Bool Bool) (T : ℕ → ι → List Bool → ℕ)
    (hU : ∀ j, 1 ≤ j → ∀ I w, IsCode I w → ∃ out, IsSearchOutput (valid I) out ∧
      HMBinPacking.OutputsWithin U (encNat j ++ pre w) out (T j I w))
    (β : ℕ → ℝ) (hβ : Tendsto β atTop (𝓝 0)) (h : ℕ → ℕ → ℝ)
    (hh : ∀ j, Tendsto (fun k => h j k / k) atTop (𝓝 0)) (c : ℕ)
    (hT : ∀ j, 1 ≤ j → ∀ I w, IsCode I w →
      (T j I w : ℝ) ≤ (2 : ℝ) ^ (β j * κ I + h j (κ I)) * (w.length : ℝ) ^ c)
    (Mfb : Turing.TM2ComputableAux Bool Bool) (f : ℕ → ℕ) (hf : Computable f) (c₀ : ℕ)
    (hfb : ∀ I w, IsCode I w → ∃ out, IsSearchOutput (valid I) out ∧
      HMBinPacking.OutputsWithin Mfb w out (f (κ I) * w.length ^ c₀))
    (hsim : ∃ Msim : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets Msim ∧ ∃ a : ℕ,
      ∀ I w, IsCode I w → ∃ out, IsSearchOutput (valid I) out ∧
        HMBinPacking.OutputsWithin Msim w out
          (P I w + ((max 1 (κ I) + 1) *
            (((Finset.Icc 1 (max 1 (κ I))).inf' (by simp) fun j => T j I w) + 1)) ^ a)) :
    ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧
      ∃ (c' : ℕ) (g : ℕ → ℕ), Tendsto (fun k => (g k : ℝ) / k) atTop (𝓝 0) ∧
        ∀ I w, IsCode I w → ∃ out, IsSearchOutput (valid I) out ∧
          HMBinPacking.OutputsWithin M w out (P I w + 2 ^ g (κ I) * w.length ^ c') := by sorry

end RevRedSAT
