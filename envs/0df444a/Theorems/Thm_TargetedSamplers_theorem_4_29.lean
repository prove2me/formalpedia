-- Prove2me | Theorems.Thm_TargetedSamplers_theorem_4_29
-- name    : TargetedSamplers.theorem_4_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:10:30.454199+00:00
-- url     : https://prove2.me/theorems/41aa1e2e-1242-4e82-a953-29353b87caab
-- title:
--   Theorem 4.29 — quantified derandomization of prRTC from uniform hardness
-- statement:
--   Let $\epsilon,\beta>0$ and let $T,Q,C$ be time-constructible with $n\le Q(n)\le2^{n^{1-\epsilon}}$. Let $W(n)=\Theta(C(n)^{1/(1-\beta)})$ and $d_f(n)=\mathrm{polylog}(W(n))$. Assume that some $f:\{0,1\}^n\to\{0,1\}^n$ is computed by a sufficiently uniform circuit family of width $W(n)$ and depth $d_f(n)$, and that $f$ is hard on all but finitely many inputs against $\mathsf F(\mathsf{MA}\cap\mathsf{AM})_R\mathsf{TISP}[T',S]$ for every choice of constants in
--   $$T'=\tilde O(W^\beta\cdot T),\qquad S=O(C+W^\beta\log Q(C)),\qquad R=\Theta(\log Q(C)).$$
--   Then
--   $$\mathrm{prRTC}_Q[T,C]\subseteq\mathrm{prDTIME}[\tilde O(W^\beta\cdot T)].$$
--
--   Applied twice, once to the oracle problem and once to the outer algorithm of Lemma 4.16, it gives Theorem 4.30.
--
--   Differences from the source:
--   - reading: "hard against F(MA∩AM)_R TISP[T′, S]" with T′ = Õ(W^β·T), S = O(…), R = Θ(…) → hard against the class for every choice of the constants K, k; reason: the class with Õ, O, Θ is the union over the constants; machines with fewer coins, less time or space are also in a larger class, so the lower half of Θ adds nothing
--   - reading: machines in time T(n) and space S(n) → time T(n) + K and space S(n) + K for every constant K (HardAgainst); reason: on the log-cost RAM a halting run costs at least 1 and the first instruction runs on every input, so with exact bounds T(0) = 0 or T(1) = 1 leaves only machines answering ⊥ at once and makes every f hard
--   - reading: W = Θ(C^{1/(1−β)}), d_f = polylog(W) → any W with K₁C^{1/(1−β)} ≤ W ≤ K₂C^{1/(1−β)} for all n ≥ N, any d_f ≤ K(log₂ W + 1)^k; reason: Θ and polylog name such functions; Θ is asymptotic, and a bound at every n would exclude C(0) = 0, since a width is at least 1
--   - reading: S ≤ Õ(C + W/C^ϵ), R ≤ Θ(C^{1−ϵ}) → omitted; reason: these are size remarks on the class parameters, implied by n ≤ Q(n) ≤ 2^{n^{1−ϵ}}; the class is defined by the first expressions
--   - reading: "runs in time t" on an unspecified RAM → time at most budget = K·(t+1)·(log₂(n+t+2)+1)^k on the log-cost RAM; reason: the paper fixes no cost model; the log-cost RAM differs from a word RAM by polylogarithmic factors
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Theorem 4.29, p.41 (pdf p.43)

import Mathlib
import Definitions.Def_TargetedSamplers_IsSufficientlyUniform
import Definitions.Def_TargetedSamplers_HardAgainst
import Definitions.Def_TargetedSamplers_InPrRTC
import Definitions.Def_TargetedSamplers_InPrDTIME

namespace TargetedSamplers

/-- Theorem 4.29 (quantified derandomization of prRTC from uniform hardness assumptions) (Chen,
Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission, manuscript sha256 599d0a59…, p.41).
For all constants `ϵ, β > 0` and time-constructible `T, Q, C` with `n ≤ Q(n) ≤ 2^{n^{1−ϵ}}`, let
`W(n) = Θ(C(n)^{1/(1−β)})` and `d_f(n) = polylog(W(n))`. If some `f : {0,1}ⁿ → {0,1}ⁿ` is computed by
a sufficiently uniform circuit family of width `W(n)` and depth `d_f(n)` and is hard against
`F(MA ∩ AM)_R TISP[T′, S]` on all but finitely many inputs, where `T′ = Õ(W^β · T)`,
`S = O(C + W^β · log Q(C))`, `R = Θ(log Q(C))`, then `prRTC_Q[T, C] ⊆ prDTIME[Õ(W^β · T)]`.

**Formalization Note** `W` is any function within constant factors of `C^{1/(1−β)}` for all large
`n`, and `d_f` any function bounded by `K(log₂ W + 1)^k`. "Hard against the class with `T′ = Õ(W^β·T)`, `S = O(…)`,
`R = Θ(…)`" is read as hardness against every choice of the constants (the class is the union over
them; more coins, time or space only enlarge the class, so the lower half of `Θ` adds nothing).
The printed bounds `S ≤ Õ(C + W/C^ϵ)` and `R ≤ Θ(C^{1−ϵ})` are consequences and are omitted.
Time in the classes is `budget`, which
contains the `Õ` of the conclusion. -/
theorem theorem_4_29 (ϵ β : ℝ) (hϵ : 0 < ϵ) (hβ : 0 < β)
    (T Q C : ℕ → ℕ) (hTc : TimeConstructible T) (hQc : TimeConstructible Q)
    (hCc : TimeConstructible C)
    (hQ : ∀ n : ℕ, n ≤ Q n ∧ (Q n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) ^ (1 - ϵ)))
    (W : ℕ → ℕ)
    (hW : ∃ (K₁ K₂ : ℝ) (N : ℕ), 0 < K₁ ∧ 0 < K₂ ∧ ∀ n : ℕ, N ≤ n →
      K₁ * (C n : ℝ) ^ (1 / (1 - β)) ≤ W n ∧ (W n : ℝ) ≤ K₂ * (C n : ℝ) ^ (1 / (1 - β)))
    (d : ℕ → ℕ) (hd : ∃ K k : ℕ, ∀ n, d n ≤ K * (Nat.log 2 (W n) + 1) ^ k)
    (F : (n : ℕ) → LayeredCircuit n) (f : List Bool → List Bool)
    (hF : IsSufficientlyUniform F d W (fun n => n)) (hf : Computes F f)
    (hhard : ∀ K k : ℕ, HardAgainst f
      (fun n => K * (Nat.clog 2 (Q (C n)) + 1))
      (fun n => ⌈(K : ℝ) * (W n : ℝ) ^ β * T n * (Nat.log 2 (n + W n + T n + 2) + 1) ^ k⌉₊)
      (fun n => ⌈(K : ℝ) * (C n + (W n : ℝ) ^ β * Real.logb 2 (Q (C n)))⌉₊)) :
    ∀ L : KarpLiptonOM.PromiseProblem, InPrRTC (fun c => (Q c : ℝ)) T C L →
      InPrDTIME (fun n => ⌈(W n : ℝ) ^ β * T n⌉₊) L := by sorry

end TargetedSamplers
