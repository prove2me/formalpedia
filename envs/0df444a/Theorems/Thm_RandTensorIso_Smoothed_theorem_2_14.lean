-- Prove2me | Theorems.Thm_RandTensorIso_Smoothed_theorem_2_14
-- name    : RandTensorIso.Smoothed.theorem_2_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:39:33.704367+00:00
-- url     : https://prove2.me/theorems/13d30149-407f-4990-8354-c2642d2e7097
-- title:
--   Theorem 2.14 — smoothed analysis of the unitary orbit approximation problem, explicit constants
-- statement:
--   Let $\xi$ be a mean-zero, variance-one sub-Gaussian distribution on $\mathbb C$, let $M\in\mathbb C^{n\times n\times n}$ have i.i.d. entries $m_{ijk}\sim\xi$, let $F$ be a tensor with $\|F\|_F\le n^D$ for an integer $D\ge1$, and $A=F+M$. Then there is $C>0$, depending only on $K_\xi,\chi_\xi,D$, such that for sufficiently large $n$, with probability at least $1-Cn^{-1/2}$, simultaneously for every $B\in\mathbb C^{n\times n\times n}$ and every rational $0<\varepsilon\le10^{-10}n^{-6D-1/2}$, Algorithm 3 run on $A,B$ with parameters $(D,n^{1-4D},\varepsilon)$ outputs YES if $\operatorname{dist}_{\mathbb C}(A,B)<\varepsilon$, with a witness $(\hat L,\hat R,\hat T)\in U(n)^3$ with entries in $\mathbb Q(i)$ and $\|(\hat L,\hat R,\hat T)\curvearrowright A-B\|_F\le10^{11}n^{7D+1}\varepsilon$, and outputs NO if $\operatorname{dist}_{\mathbb C}(A,B)>10^{11}n^{7D+1}\varepsilon$. With these parameters it runs in time polynomial in $n$, $\log(1/\varepsilon)$ and the bit length of the truncations $\tilde A,\tilde B$, for fixed $D$.
--
--   "Run with parameters $(D,\delta,\varepsilon)$" (2.4)–(2.5): $\ell$ is the least integer with $2^{-\ell}\le\min\{\varepsilon/(400n\lceil\sqrt n\rceil),\ \delta/(384n\lceil\sqrt n\rceil^2(n^D+2n\lceil\sqrt n\rceil)^2)\}$, $\tilde A,\tilde B$ are the truncations to $\ell$ bits, and the algorithm is run on $(\tilde A,\tilde B,\delta/2,\varepsilon+4n\lceil\sqrt n\rceil2^{-\ell})$.
--
--   In Lean: one program $P$ implementing Algorithm 3 (fixed before $D$) such that for every integer $D\ge1$, (time) a constant $C_t$ bounds the steps of every such run with $n\ge1$ by $C_t(n+\log^+(1/\varepsilon)+|\tilde A|+|\tilde B|)^{C_t}+C_t$, and (correctness) for all $K,\chi$ there are $C>0$ and $N_0$ such that for every $\xi$ with $K_\xi=K$, $\chi_\xi=\chi$, every $n\ge N_0$ and every $F$, the set of $M$ for which some $B$ and some admissible $\varepsilon$ make some admissible Algorithm 3 output wrong has outer probability at most $Cn^{-1/2}$.
--
--   Differences from the source:
--   - generalization: Algorithm 3, using the numerical eigensolver of [DKRS23] and the rounding of Lemma A.2 → a program implementing the full operational relation Alg3Outputs, with correctness for every admissible numerical and rounding choice; reason: the relation retains Steps 1–6, the PDF 25 forward-error interface and all constants; the specified implementation is a permitted run, so universal correctness specializes to the printed claim
--   - reading: C > 0 depending only on K_ξ, χ_ξ and D, for sufficiently large n → C and N₀ chosen from (D, K, χ) before ξ and valid for every ξ with K_ξ = K, χ_ξ = χ; reason: the uniform reading of 'depending only on'
--   - reading: with probability at least 1 − Cn^{-1/2}, simultaneously for every B and every rational ε → outer measure of {M : some B and some admissible ε make the output wrong} ≤ C n^{-1/2}; reason: the event need not be measurable; the outer-measure bound is the stronger reading
--   - encoding: runs in time polynomial in n, log(1/ε) and the bit length of the truncations Ã, B̃, for fixed D → for every n ≥ 1, A, B and admissible ε, P halts within C_t(n + max(0, log(1/ε)) + |enc Ã| + |enc B̃|)^{C_t} + C_t steps, C_t depending on D only; reason: the paper names no machine; steps of a FinTM2 program are the time; the time claim holds on every run, not only with high probability
-- source:
--   Chizewer, Everett, Mithal, Qiao, Random tensor isomorphism under orthogonal and unitary actions: Smoothed and average-case analysis, STOC 2027 submission (manuscript sha256 f4a12b77…), pp. 30–31 (PDF 32–33), (2.4)–(2.5) and Theorem 2.14

import Mathlib
import Definitions.Def_RandTensorIso_Smoothed_Tensor
import Definitions.Def_RandTensorIso_Smoothed_Spectral
import Definitions.Def_RandTensorIso_Smoothed_SubGaussian
import Definitions.Def_RandTensorIso_Smoothed_Machine

open MeasureTheory

namespace RandTensorIso.Smoothed

/-- Theorem 2.14 (pp. 30–31). There is one program implementing Algorithm 3, run "on `A, B` with parameters
`(D, δ, ε)`" as in (2.4)–(2.5) with `δ = n^{1−4D}`: `ℓ` is the least integer with
`2^{−ℓ} ≤ min{ε/(400n⌈√n⌉), δ/(384n⌈√n⌉²(n^D + 2n⌈√n⌉)²)}` and the program reads
`(Ã, B̃, δ/2, ε + 4n⌈√n⌉2^{−ℓ})`, `Ã, B̃` the truncations to `ℓ` bits. For every integer `D ≥ 1`:
(time) on every such run with `n ≥ 1` and `0 < ε ≤ 10^{−10} n^{−6D−1/2}` it halts within a
polynomial (depending on `D` only) in `n`, `log(1/ε)` and the bit length of `Ã, B̃`;
(correctness) for every `K, χ` there are `C > 0` and `N₀` such that for every mean-zero,
variance-one sub-Gaussian `ξ` on `ℂ` with `K_ξ = K`, `χ_ξ = χ`, every `n ≥ N₀` and every `F` with
`‖F‖_F ≤ n^D`, the set of `M` for which some `B` and some admissible rational `ε` make any admissible Algorithm 3 output
on `A = F + M` wrong for `γ = 10^{11} n^{7D+1}` has outer probability at most `C n^{−1/2}`. -/
theorem theorem_2_14 :
    ∃ P : Program, ImplementsAlg3 P ∧ ∀ D : ℕ, 1 ≤ D →
      let δ : ℕ → ℚ := fun n => (n : ℚ) ^ ((1 : ℤ) - 4 * D)
      let ℓ : ℕ → ℚ → ℕ := fun n ε => sInf {k : ℕ | (2 : ℝ)⁻¹ ^ k ≤
        min ((ε : ℝ) / (400 * n * ⌈Real.sqrt n⌉₊))
          ((δ n : ℝ) / (384 * n * ⌈Real.sqrt n⌉₊ ^ 2 * ((n : ℝ) ^ D + 2 * n * ⌈Real.sqrt n⌉₊) ^ 2))}
      let run : (n : ℕ) → Tensor3 n → Tensor3 n → ℚ → List Bool := fun n A B ε =>
        alg3Input (truncT (ℓ n ε) A) (truncT (ℓ n ε) B) (δ n / 2)
          (ε + 4 * n * ⌈Real.sqrt n⌉₊ * (2 : ℚ)⁻¹ ^ (ℓ n ε))
      (∃ Ct : ℕ, ∀ (n : ℕ), 1 ≤ n → ∀ (A B : Tensor3 n) (ε : ℚ), 0 < ε →
          (ε : ℝ) ≤ (n : ℝ) ^ (-(6 * (D : ℝ) + 1 / 2)) / 10 ^ 10 →
          ∃ (out : List Bool) (T : ℕ), P.HaltsWith (run n A B ε) out T ∧
            (T : ℝ) ≤ Ct * ((n : ℝ) + max 0 (Real.log (1 / (ε : ℝ))) +
              (encGTensor (truncT (ℓ n ε) A)).length + (encGTensor (truncT (ℓ n ε) B)).length) ^ Ct
              + Ct) ∧
      ∀ K χ : ℝ, ∃ (C : ℝ) (N₀ : ℕ), 0 < C ∧
        ∀ (ξ : ProbabilityMeasure ℂ), IsStdSubGaussian (ξ : Measure ℂ) →
        subGaussConst (ξ : Measure ℂ) = K → chiConst (ξ : Measure ℂ) = χ →
        ∀ (n : ℕ), N₀ ≤ n → ∀ (F : Tensor3 n), frob F ≤ (n : ℝ) ^ D →
          tensorLaw ξ n {M : Tensor3 n | ∃ (B : Tensor3 n) (ε : ℚ), 0 < ε ∧
              (ε : ℝ) ≤ (n : ℝ) ^ (-(6 * (D : ℝ) + 1 / 2)) / 10 ^ 10 ∧
              ∃ out : List Bool,
                Alg3Outputs (truncT (ℓ n ε) (F + M)) (truncT (ℓ n ε) B) (δ n / 2)
                  (ε + 4 * n * ⌈Real.sqrt n⌉₊ * (2 : ℚ)⁻¹ ^ (ℓ n ε)) out ∧
                ¬ GappedCorrect (F + M) B ε (10 ^ 11 * (n : ℝ) ^ (7 * D + 1)) out} ≤
            ENNReal.ofReal (C * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by sorry

end RandTensorIso.Smoothed
