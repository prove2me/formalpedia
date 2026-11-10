-- Prove2me | Theorems.Thm_RandTensorIso_Smoothed_theorem_1_1
-- name    : RandTensorIso.Smoothed.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:39:15.648206+00:00
-- url     : https://prove2.me/theorems/bb9f7bb8-2b07-4a15-9f74-417927e6f57e
-- title:
--   Theorem 1.1 — smoothed analysis of the unitary orbit approximation problem
-- statement:
--   **Theorem 1.1.** Fix a mean-zero, variance-one sub-Gaussian distribution $\xi$ on $\mathbb C$ and an integer $D\ge1$. There exist a constant $c>0$ and a deterministic algorithm which, given a rational $\varepsilon$ with $0<\varepsilon\le cn^{-6D-1/2}$, a tensor $A=F+M\in\mathbb C^{n\times n\times n}$, where $F$ is deterministic with $\|F\|_F\le n^D$ and $M$ has i.i.d. entries $m_{ijk}\sim\xi$, and an arbitrary $B\in\mathbb C^{n\times n\times n}$, each specified to $O(\log(n/\varepsilon))$ bits of precision, runs in time polynomial in $n$ and $\log(1/\varepsilon)$, and, with probability $1-O(n^{-1/2})$ over the choice of $M$, simultaneously for all such $B$ and $\varepsilon$, distinguishes
--   $$\operatorname{dist}_{\mathbb C}(A,B)<\varepsilon\quad\text{from}\quad\operatorname{dist}_{\mathbb C}(A,B)>\gamma\varepsilon,\qquad\gamma=O(n^{7D+1}).$$
--   In the former case, the algorithm also outputs a witness $(\hat L,\hat R,\hat T)\in U(n)^3$ with entries in $\mathbb Q(i)$ such that $\|(\hat L,\hat R,\hat T)\curvearrowright A-B\|_F\le\gamma\varepsilon$. The constant $c$ and the implied constants depend only on $D$, $K_\xi$ and $\chi_\xi$.
--
--   **Lean form.** For every integer $D\ge1$ and all real $K,\chi$ there are $c>0$, a program $P$, a computable precision rule $\ell(n,\varepsilon)$ and constants $C_{\rm bits},C_{\rm time}\in\mathbb N$, $C_{\rm fail}>0$ and $C_\gamma\ge1$ such that:
--   1. $\ell(n,\varepsilon)\le C_{\rm bits}\log(n/\varepsilon)+C_{\rm bits}$ for every $n\ge1$ and rational $0<\varepsilon\le cn^{-6D-1/2}$;
--   2. for every $n\ge1$, all $A,B\in\mathbb C^{n\times n\times n}$ and every such $\varepsilon$, $P$ on input ($n$; $A$ and $B$ specified to $\ell(n,\varepsilon)$ bits after the binary point; $\varepsilon$) halts within $C_{\rm time}(n+\log^+(1/\varepsilon))^{C_{\rm time}}+C_{\rm time}$ steps;
--   3. for every mean-zero, variance-one sub-Gaussian $\xi$ on $\mathbb C$ with $K_\xi=K$ and $\chi_\xi=\chi$, every $n\ge1$ and every $F$ with $\|F\|_F\le n^D$, the set of $M$ for which some $B$ and some such $\varepsilon$ make the output on $A=F+M$ incorrect for Problem 1 with $\gamma=C_\gamma n^{7D+1}$ has outer probability at most $C_{\rm fail}n^{-1/2}$.
--
--   The witness bound is measured against the exact $A$ and $B$, not their truncations; the program never sees $F$, $M$, $\xi$ or the exact tensors.
--
--   Differences from the source:
--   - reading: Fix ξ … There exist c > 0 and a deterministic algorithm …; the constant c and the implied constants depend only on D, K_ξ and χ_ξ → c, the program, the precision rule and all constants are chosen from (D, K, χ) before ξ and work for every ξ with K_ξ = K and χ_ξ = χ; reason: the uniform reading of 'depend only on D, K_ξ, χ_ξ' (stronger than choosing them after ξ)
--   - encoding: a deterministic algorithm … runs in time polynomial in n and log(1/ε) → a Mathlib Turing.FinTM2 program over bits that halts within C_time(n + max(0, log(1/ε)))^{C_time} + C_time steps on every input of the stated form (every A, B, every admissible ε); reason: the paper names no machine; steps are the time; the positive part only matters when ε > 1, where log(1/ε) is bounded below by −log c
--   - encoding: A and B each specified to O(log(n/ε)) bits of precision; ε given as a rational → input = n, then A and B as fixed-point ℓ-bit truncations (ℓ written before each), then ε; ℓ = ℓ(n, ε) ≤ C_bits log(n/ε) + C_bits is a computable rule fixed with the program; reason: the truncation model of p. 6 and §2.3: the algorithm chooses the precision from ε; an ℓ-bit truncation is written with exactly ℓ fractional digits; computability prevents the precision selection from supplying an oracle
--   - reading: with probability 1 − O(n^{-1/2}) over M, simultaneously for all such B and ε → for every n ≥ 1, the outer measure of {M : some B and some admissible ε make the output incorrect} is ≤ C_fail n^{-1/2}; reason: the event need not be measurable; the outer-measure bound is the stronger reading; O(·) is one constant for all n
--   - encoding: γ = O(n^{7D+1}); 'distinguishes' with a witness in the former case → γ = C_γ n^{7D+1} with C_γ ≥ 1 and C_fail > 0; correct = (dist < ε → YES with unitary ℚ(i) witness, ‖·‖_F ≤ γε) ∧ (dist > γε → NO); reason: explicit constant; between the thresholds any output is allowed, as in Problem 1; the implicit constants may be enlarged to these positive normalizations
-- source:
--   Chizewer, Everett, Mithal, Qiao, Random tensor isomorphism under orthogonal and unitary actions: Smoothed and average-case analysis, STOC 2027 submission (manuscript sha256 f4a12b77…), p. 6 (PDF 8), Theorem 1.1

import Mathlib
import Definitions.Def_RandTensorIso_Smoothed_Tensor
import Definitions.Def_RandTensorIso_Smoothed_SubGaussian
import Definitions.Def_RandTensorIso_Smoothed_Machine

open MeasureTheory

namespace RandTensorIso.Smoothed

/-- Theorem 1.1 (p. 6). For every integer `D ≥ 1` and all values `K, χ` of `K_ξ, χ_ξ` there are
`c > 0`, one program, a computable precision rule `ℓ(n, ε) ≤ C_bits log(n/ε) + C_bits`, and constants
`C_time, C_fail, C_γ` such that for every mean-zero, variance-one sub-Gaussian `ξ` on `ℂ` with
`K_ξ = K`, `χ_ξ = χ`, every `n ≥ 1` and every `F` with `‖F‖_F ≤ n^D`:
(time) on input `n`, `A` and `B` specified to `ℓ(n, ε)` bits after the binary point, and a
rational `0 < ε ≤ c n^{−6D−1/2}`, the program halts within `C_time (n + log(1/ε))^{C_time} + C_time`
steps, for every `A, B`;
(correctness) with `A = F + M`, `M` with i.i.d. `ξ` entries, the set of `M` for which some `B`
and some admissible `ε` make the output wrong (Problem 1 with `γ = C_γ n^{7D+1}`) has outer
probability at most `C_fail n^{−1/2}`. -/
theorem theorem_1_1 :
    ∀ D : ℕ, 1 ≤ D → ∀ K χ : ℝ,
    ∃ (c : ℝ) (P : Program) (prec : ℕ → ℚ → ℕ) (Cbits Ctime : ℕ) (Cfail Cγ : ℝ), 0 < c ∧ 0 < Cfail ∧ 1 ≤ Cγ ∧ Computable₂ prec ∧
      (∀ (n : ℕ) (ε : ℚ), 1 ≤ n → 0 < ε → (ε : ℝ) ≤ c * (n : ℝ) ^ (-(6 * (D : ℝ) + 1 / 2)) →
        (prec n ε : ℝ) ≤ Cbits * Real.log (n / (ε : ℝ)) + Cbits) ∧
      (∀ (n : ℕ), 1 ≤ n → ∀ (A B : Tensor3 n) (ε : ℚ), 0 < ε →
        (ε : ℝ) ≤ c * (n : ℝ) ^ (-(6 * (D : ℝ) + 1 / 2)) →
        ∃ (out : List Bool) (T : ℕ), P.HaltsWith (goalInput (prec n ε) A B ε) out T ∧
          (T : ℝ) ≤ Ctime * ((n : ℝ) + max 0 (Real.log (1 / (ε : ℝ)))) ^ Ctime + Ctime) ∧
      ∀ (ξ : ProbabilityMeasure ℂ), IsStdSubGaussian (ξ : Measure ℂ) →
        subGaussConst (ξ : Measure ℂ) = K → chiConst (ξ : Measure ℂ) = χ →
        ∀ (n : ℕ), 1 ≤ n → ∀ (F : Tensor3 n), frob F ≤ (n : ℝ) ^ D →
          tensorLaw ξ n {M : Tensor3 n | ∃ (B : Tensor3 n) (ε : ℚ), 0 < ε ∧
              (ε : ℝ) ≤ c * (n : ℝ) ^ (-(6 * (D : ℝ) + 1 / 2)) ∧
              ¬ ∃ (out : List Bool) (T : ℕ), P.HaltsWith (goalInput (prec n ε) (F + M) B ε) out T ∧
                GappedCorrect (F + M) B ε (Cγ * (n : ℝ) ^ (7 * D + 1)) out} ≤
            ENNReal.ofReal (Cfail * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by sorry

end RandTensorIso.Smoothed
