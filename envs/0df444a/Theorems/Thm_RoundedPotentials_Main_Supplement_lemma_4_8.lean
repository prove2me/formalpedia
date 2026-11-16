-- Prove2me | Theorems.Thm_RoundedPotentials_Main_Supplement_lemma_4_8
-- name    : RoundedPotentials.Main.Supplement.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:09:09.272205+00:00
-- url     : https://prove2.me/theorems/20df5bdf-af09-43d1-85cf-d2146ae053dc
-- title:
--   Lemma 4.8 — Batch verification time
-- statement:
--   Let $\mathrm{MM}$ be a deterministic word-RAM program that multiplies an $r\times d$ by a $d\times d$ natural matrix within $T(r,d)$ steps, at every word size at least $K_0\lceil\log_2(\text{input magnitude})\rceil$; this $T$ is the paper's $\mathrm{MM}_d(r)$. Fix an exponent $D$.
--
--   There are a deterministic program and constants $C,K$ with the following property. Let $n\ge2$, $1\le W\le n^D$, and let $c$ be a capacity matrix with entries at most $W$. Let $B$ be an integer bucket size with $1\le B\le n$. Let $Q$ be any nonempty set of $q$ ordered pairs of distinct vertices, each pair with a claimed value $0\le p_a\le(n-1)W$ and grid indices $i^a_u\in[0,(2n-1)Q_0]$, where $Q_0=32n^2W$. Then the program performs all excess tests (7) for the pairs in $Q$, outputting for each pair whether
--   $$|\mathrm{ex}_{g^a}(v)-p_a(\mathbf 1[v=s_a]-\mathbf 1[v=t_a])|\le\tfrac1{8n}\qquad\text{for all }v,$$
--   within
--   $$C(\lfloor\log_2 n\rfloor+1)^K\bigl(\mathrm{MM}_n(q\lceil n/B\rceil)+qnB\bigr)+C$$
--   steps, that is, in $\widetilde O(\mathrm{MM}_n(q\lceil n/B\rceil)+qnB)$ time.
--
--   This trades the bucket size against rectangular matrix multiplication. It is the time bound behind Corollary 4.9.
--
--   **Formalization Note** Machine: `DynConnWC.Program` with `MinKCutII_Main_Runs`. The polylogarithmic factor is $(\lfloor\log_2 n\rfloor+1)^K$, and the word size is $K\lceil\log_2(\cdot)\rceil$ of the input and the time bound.
--
--   Differences from the source:
--   - reading: MM_d(r_rows), the time to multiply an r_rows × d matrix by a d × d matrix → T(r, d) for an arbitrary deterministic multiplication program MM that is correct within T(r, d) steps at every word size ≥ K₀⌈log₂ inputMag⌉; reason: MM_d is the running time of the multiplication routine the batch uses; the lemma holds for every such routine
--   - encoding: all excess tests for the pairs in Q (after the checks (6) of Algorithm 1) → the list of pass bits of the tests (7)/(12) for given blocks satisfying 0 ≤ p ≤ (n−1)W and 0 ≤ i_u ≤ (2n−1)Q₀; Q a nonempty duplicate-free list of pairs of distinct vertices; reason: the tests run on guesses that passed the range checks; the bound is vacuous for q = 0
--   - encoding: Õ(·) time; polynomially bounded capacities → C(⌊log₂ n⌋+1)^K(·) + C steps on the word RAM DynConnWC.Program; ∀ D, W ≤ n^D; reason: explicit form; the standing assumption of §1.1
--   - encoding: ⌈n/B⌉ → (n + B − 1) / B in ℕ; reason: same value
-- source:
--   Ohad Trabelsi, STOC 2027 submission #1650 (October 2026), p. 24, Lemma 4.8

import Mathlib
import Definitions.Def_RoundedPotentials_Main_Supplement_Verification

namespace RoundedPotentials.Main.Supplement

open RoundedPotentials.Main DynConnWC MinKCutII.Main MultStretchAPASP.Weighted

theorem lemma_4_8 (D : ℕ) (MM : Program) (K₀ : ℕ) (T : ℕ → ℕ → ℝ) (hMM : MMProgram MM K₀ T) :
    ∃ Q : Program, IsDeterministic Q ∧ ∃ C K : ℕ,
      ∀ (n W B : ℕ), 2 ≤ n → 1 ≤ W → W ≤ n ^ D → 1 ≤ B → B ≤ n →
      ∀ (cap : Fin n → Fin n → ℕ), (∀ u v, cap u v ≤ W) →
      ∀ (bs : List (Block n)), 1 ≤ bs.length → (bs.map (fun b => (b.s, b.t))).Nodup →
        (∀ b ∈ bs, BlockPromise n W b) →
          let x := batchInput n W B cap bs
          let q := bs.length
          let Tq : ℝ := C * ((Nat.log 2 n : ℝ) + 1) ^ K *
            (T (q * ((n + B - 1) / B)) n + q * n * B) + C
          let Wd := wordSize K x Tq
          ∀ ω : ℕ → Fin (2 ^ Wd),
            HaltsWithin Wd Q x ω Tq ∧ finalOutput Wd Q x ω = excessAnswers n W cap bs := by sorry

end RoundedPotentials.Main.Supplement
