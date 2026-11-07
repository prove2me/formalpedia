-- Prove2me | Theorems.Thm_TargetedSamplers_theorem_4_30
-- name    : TargetedSamplers.theorem_4_30
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:10:22.849315+00:00
-- url     : https://prove2.me/theorems/945ab8ea-6296-4788-814c-9c6f4552fa51
-- title:
--   Theorem 4.30 — overhead-free quantified derandomization from uniform hardness (corrected: prBPTIME error is Q/2^T)
-- statement:
--   There are universal constants $c_0,c_1,c_2,c_3>0$ with the following property. Let $T:\mathbb N\to\mathbb N$ be monotone and time-constructible with $T(n)\ge n$, and let $0<\epsilon<1$. Assume that for both
--   $$T_0=\lceil T^{1+c_0\epsilon^2}\rceil\quad\text{and}\quad T_0=n,$$
--   with $W_{T_0}=\lceil T_0^{1+c_1\epsilon}\rceil$, there is a function $f_{T_0}:\{0,1\}^n\to\{0,1\}^n$ satisfying two conditions:
--
--   1. it is computed by a sufficiently uniform circuit family of width $w(n)\le K\,W_{T_0}(n)$ and depth at most $K(\log_2T_0+1)^k$, for some constants $K,k$;
--   2. it is hard, on all but finitely many inputs, against the class
--   $$\mathsf F(\mathsf{MA}\cap\mathsf{AM})_{\lceil T_0^{1-\epsilon^4}\rceil}\,\mathsf{TISP}\big[\lceil W_{T_0}\cdot T_0^{c_2\epsilon}\rceil,\ \lceil W_{T_0}/T_0^{\epsilon^4}\rceil\big]$$
--   (time and space up to an additive constant, Definition 4.20 as formalized).
--
--   Then
--   $$\mathrm{prBPTIME}_{2^{(1-\epsilon)T}}[T]\subseteq\mathrm{prDTIME}[\lceil T^{1+c_3\epsilon}\rceil].$$
--
--   So promise problems solved in time $T$ with $T$ coins and two-sided error $2^{-\epsilon T}$ are solved deterministically in time $T^{1+O(\epsilon)}$. The hardness assumption is against uniform probabilistic non-deterministic algorithms whose space is below the circuit width, not against non-uniform circuits.
--
--   **Formalization Note** The proof (p.42) applies Theorem 4.29 with $\epsilon'=\epsilon^4$ and $\beta=\epsilon$. As written, that application needs $\epsilon$ below a constant, and it needs consistency of the reconstruction at inputs outside the promise. The statement is kept as printed. The classes measure time on a log-cost RAM up to polylogarithmic factors, which the factors $T^{O(\epsilon)}$ absorb.
--
--   Differences from the source:
--   - reading: the four O(·) (T₀ = T^{1+O(ϵ²)}, width T₀^{1+O(ϵ)}, time W·T₀^{O(ϵ)}, conclusion T^{1+O(ϵ)}) → universal constants c₀, c₁, c₂, c₃ > 0 chosen before T and ϵ; reason: an O(ϵ) exponent is c·ϵ with a fixed c; the theorem chooses c
--   - reading: width W_{T₀} = T₀(n)^{1+O(ϵ)}, depth polylog T₀ → width w(n) ≤ K·⌈T₀^{1+c₁ϵ}⌉ and depth ≤ K(log₂ T₀ + 1)^k, with K, k chosen with the family; hardness parameters use W_{T₀} := ⌈T₀^{1+c₁ϵ}⌉; reason: a width that is a power of 2 and holds the 2n literals cannot equal T₀^{1+c₁ϵ} in general, so without K the hypothesis would be unsatisfiable at T₀ = n
--   - reading: machines in time T(n) and space S(n) → time T(n) + K and space S(n) + K for every constant K (HardAgainst); reason: on the log-cost RAM a halting run costs at least 1 and the first instruction runs on every input, so with exact bounds T(0) = 0 or T(1) = 1 leaves only machines answering ⊥ at once and makes every f hard
--   - encoding: T^{1+O(ϵ²)}, T₀^{1−ϵ⁴}, W·T₀^{O(ϵ)}, W/T₀^{ϵ⁴}, T^{1+O(ϵ)} → real powers rounded up to naturals; reason: coin counts and bounds are natural numbers; rounding down could give 0
--   - generalization: monotone increasing T → Monotone T (non-decreasing); reason: the proof uses only monotonicity; every strictly increasing T is an instance
--   - correction: prBPTIME_Q[T]: "error probability δ = Q/T" (Theorem 1.6, p.5) → error at most Q(T(n))/2^{T(n)}; reason: counterexample: with Q = 2^{(1−ϵ)T}, Q/T ≥ 1 for large T, so the printed class contains every promise problem, e.g. the halting problem, which no bounded-error algorithm decides; Definition 4.1 and §4.1 use Q/2^T
--   - reading: "runs in time t" on an unspecified RAM → time at most budget = K·(t+1)·(log₂(n+t+2)+1)^k on the log-cost RAM; reason: the paper fixes no cost model; the log-cost RAM differs from a word RAM by polylogarithmic factors
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Theorem 4.30, p.42 (pdf p.44); Theorem 1.6, p.5 (pdf p.7)

import Mathlib
import Definitions.Def_TargetedSamplers_IsSufficientlyUniform
import Definitions.Def_TargetedSamplers_HardAgainst
import Definitions.Def_TargetedSamplers_InPrBPTC
import Definitions.Def_TargetedSamplers_InPrDTIME

namespace TargetedSamplers

/-- Theorem 4.30 (Theorem 1.6, restated) (Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027
submission, manuscript sha256 599d0a59…, p.42). For every increasing time-constructible
`T : ℕ → ℕ` with `T(n) ≥ n` and every constant `0 < ϵ < 1`: assume that for both
`T₀ = T^{1+O(ϵ²)}` and `T₀ = n` there is `f_{T₀} : {0,1}ⁿ → {0,1}ⁿ` computed by a sufficiently uniform
circuit family of width `W_{T₀} = T₀(n)^{1+O(ϵ)}` and depth `polylog T₀`, hard against
`F(MA ∩ AM)_{T₀^{1−ϵ⁴}} TISP[W_{T₀} · T₀^{O(ϵ)}, W_{T₀}/T₀^{ϵ⁴}]` on all but finitely many inputs. Then
`prBPTIME_{2^{(1−ϵ)T}}[T] ⊆ prDTIME[T^{1+O(ϵ)}]`.

**Formalization Note** The four `O(·)` are universal constants `c₀, c₁, c₂, c₃ > 0` chosen before
`T` and `ϵ`. With `W := ⌈T₀^{1+c₁ϵ}⌉`, the family has width `w(n) ≤ K · W(n)` (a power of 2 that
holds the `2n` literals cannot in general equal `T₀^{1+c₁ϵ}`; `K` and the depth exponent `k` belong
to the family), and hardness is against `R = ⌈T₀^{1−ϵ⁴}⌉` coins, time `⌈W · T₀^{c₂ϵ}⌉` and space
`⌈W / T₀^{ϵ⁴}⌉`, time and space up to an additive constant (`HardAgainst`). "Increasing" is
`Monotone`; real powers are rounded up; `T₀ = n` is the identity.
`prBPTIME_Q[T]` has error `Q/2^T` (Theorem 1.6 prints `Q/T`, which at `Q = 2^{(1−ϵ)T}` imposes no
condition). Time in the classes is `budget`. -/
theorem theorem_4_30 : ∃ c₀ c₁ c₂ c₃ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧
    ∀ T : ℕ → ℕ, Monotone T → TimeConstructible T → (∀ n, n ≤ T n) →
    ∀ ϵ : ℝ, 0 < ϵ → ϵ < 1 →
    (∀ T₀ ∈ ({fun n => ⌈(T n : ℝ) ^ (1 + c₀ * ϵ ^ 2)⌉₊, fun n => n} : Set (ℕ → ℕ)),
      ∃ (f : List Bool → List Bool) (F : (n : ℕ) → LayeredCircuit n) (w d : ℕ → ℕ) (K k : ℕ),
        IsSufficientlyUniform F d w (fun n => n) ∧ Computes F f ∧
        (∀ n, w n ≤ K * ⌈(T₀ n : ℝ) ^ (1 + c₁ * ϵ)⌉₊) ∧
        (∀ n, d n ≤ K * (Nat.log 2 (T₀ n) + 1) ^ k) ∧
        HardAgainst f (fun n => ⌈(T₀ n : ℝ) ^ (1 - ϵ ^ 4)⌉₊)
          (fun n => ⌈(⌈(T₀ n : ℝ) ^ (1 + c₁ * ϵ)⌉₊ : ℝ) * (T₀ n : ℝ) ^ (c₂ * ϵ)⌉₊)
          (fun n => ⌈(⌈(T₀ n : ℝ) ^ (1 + c₁ * ϵ)⌉₊ : ℝ) / (T₀ n : ℝ) ^ (ϵ ^ 4)⌉₊)) →
    ∀ L : KarpLiptonOM.PromiseProblem, InPrBPTIME (fun c => (2 : ℝ) ^ ((1 - ϵ) * c)) T L →
      InPrDTIME (fun n => ⌈(T n : ℝ) ^ (1 + c₃ * ϵ)⌉₊) L := by sorry

end TargetedSamplers
