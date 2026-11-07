-- Prove2me | Theorems.Thm_TargetedSamplers_proposition_4_26
-- name    : TargetedSamplers.proposition_4_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:08:03.791916+00:00
-- url     : https://prove2.me/theorems/3d4b3671-fa07-476b-a40f-a9d6ceddc6b9
-- title:
--   Proposition 4.26 — a reconstructive targeted hitting-set generator
-- statement:
--   Let $f:\{0,1\}^n\to\{0,1\}^n$ be computed by a sufficiently uniform circuit family of width $W_f(n)$ and depth $d_f(n)$. Let $\epsilon,\beta\in(0,1)$, and let $Q$ be time-constructible with $n\le Q(n)\le2^{n^{1-\epsilon}}$. Then there are a deterministic algorithm $H_f$, a probabilistic oracle machine $\mathrm{Rec}$, a block length $m=\tilde O(W_f^{1-\beta})$ and functions $R,T,S$ such that:
--
--   1. **Generator.** On input $x$, $H_f$ prints a list of $\tilde O(d_f\,W_f^{\beta})$ strings of $m$ bits in time $\tilde O(d_f\,W_f)$.
--   2. **Reconstruction.** Let $\mathcal D$ be the class of Boolean oracles rejecting at most $Q(m)$ strings of length $m$. Relative to $\mathcal D$, $\mathrm{Rec}$ is an $\mathsf F(\mathsf{MA}\cap\mathsf{AM})_R\mathsf{TISP}[T,S]$ oracle machine consistent with $f$. For every $x$ and every $D\in\mathcal D$ that rejects all strings printed by $H_f(x)$, $\mathrm{Rec}^D$ computes $f$ at $x$.
--   3. **Resources.**
--   $$T(n)=\tilde O(d_f W_f),\qquad S(n)=\tilde O(W_f^{1-\beta}+W_f^{\beta}\log Q(m))\le\tilde O(W_f^{1-\beta}+W_f^{1-\epsilon+\epsilon\beta}).$$
--   $\mathrm{Rec}$ uses $R=O(\log Q(m))$ random bits and makes $O(d_f W_f^{\beta})$ oracle queries.
--
--   The generator is "targeted": its output depends on $x$, and any distinguisher that avoids it yields a probabilistic non-deterministic algorithm for $f$ at $x$.
--
--   Differences from the source:
--   - generalization: oracles D : {0,1}^m → {0,1} with |D⁻¹(0)| ≤ Q(m) → every oracle with at most Q(L) rejected strings of each length L; reason: the class contains every such D extended by 1 on other lengths, so consistency for the class implies consistency for every D
--   - encoding: Õ(·), O(·) → K·g·(log₂ W_f + 1)^k or budget, K·g, with +1 added to d_f and ⌈log₂ Q(m)⌉; reason: constants chosen with H_f and Rec; the +1 keeps the bounds meaningful when a factor vanishes
--   - encoding: the list H_f(x) prints → the concatenation of a list of m-bit strings; reason: strings of one fixed length can be read back from their concatenation
--   - reading: "runs in time t" on an unspecified RAM → time at most budget = K·(t+1)·(log₂(n+t+2)+1)^k on the log-cost RAM; reason: the paper fixes no cost model; the log-cost RAM differs from a word RAM by polylogarithmic factors
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Proposition 4.26, pp.35–36 (pdf pp.37–38)

import Mathlib
import Definitions.Def_TargetedSamplers_IsSufficientlyUniform
import Definitions.Def_TargetedSamplers_IsConsistentMachine
import Definitions.Def_TargetedSamplers_rejOracleClass

namespace TargetedSamplers

/-- Proposition 4.26 (a reconstructive tarHSG for quantified derandomization) (Chen, Doron, Ebtehaj,
Tell, Targeted Samplers, STOC 2027 submission, manuscript sha256 599d0a59…, pp.35–36). Let
`f : {0,1}ⁿ → {0,1}ⁿ` be computable by a sufficiently uniform circuit family of width `W_f(n)` and
depth `d_f(n)`. For all constants `ϵ, β ∈ (0,1)` and time-constructible `Q` with
`n ≤ Q(n) ≤ 2^{n^{1−ϵ}}`, there are a deterministic algorithm `H_f` and a probabilistic oracle machine
`Rec` such that for every `x ∈ {0,1}ⁿ`:

1. *Generator.* `H_f(x)` outputs a list of `Õ(d_f · W_f^β)` strings of `m` bits,
   `m = Õ(W_f^{1−β})`, in time `Õ(d_f · W_f)`.
2. *Reconstruction.* For the class `D` of `D : {0,1}^m → {0,1}` with `|D^{−1}(0)| ≤ Q(m)`, `Rec` is an
   `F(MA ∩ AM)_R TISP[T, S]` oracle machine consistent with `f`, and if `D ∈ D` rejects all strings
   `H_f(x)` prints, then `Rec^D` computes `f` at `x`. `Rec` runs in time `T(n) = Õ(d_f · W_f)` and space
   `S(n) = Õ(W_f^{1−β} + W_f^β · log Q(m)) ≤ Õ(W_f^{1−β} + W_f^{1−ϵ+ϵβ})`, uses `O(log Q(m))` random bits and makes
   `O(d_f · W_f^β)` oracle queries.

**Formalization Note** `Õ(g)` is `K · g · (log₂ W_f + 1)^k` (or `budget`), `O(g)` is `K · g`, with
`K, k` chosen together with `H_f` and `Rec`; `+ 1` is added to `d_f` and `⌈log₂ Q(m)⌉` where they may
vanish. The class `D` is
`rejOracleClass Q`. Both printed space bounds are stated. The witness length of `Rec` is its time bound, as in Definition 4.19. -/
theorem proposition_4_26 (W d : ℕ → ℕ) (F : (n : ℕ) → LayeredCircuit n)
    (hF : IsSufficientlyUniform F d W (fun n => n)) (f : List Bool → List Bool) (hf : Computes F f)
    (ϵ β : ℝ) (hϵ : 0 < ϵ) (hϵ1 : ϵ < 1) (hβ : 0 < β) (hβ1 : β < 1)
    (Q : ℕ → ℕ) (hQc : TimeConstructible Q)
    (hQ : ∀ n : ℕ, n ≤ Q n ∧ (Q n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) ^ (1 - ϵ))) :
    ∃ (H Rec : Program) (G : List Bool → List (List Bool)) (m R Tr Sr : ℕ → ℕ) (K k : ℕ),
      (∀ n : ℕ, (m n : ℝ) ≤ K * (W n : ℝ) ^ (1 - β) * (Nat.log 2 (W n) + 1) ^ k) ∧
      (∀ x : List Bool, (∀ z ∈ G x, z.length = m x.length) ∧
        ((G x).length : ℝ) ≤
          K * (d x.length + 1) * (W x.length : ℝ) ^ β * (Nat.log 2 (W x.length) + 1) ^ k ∧
        H.RunsIn (Tapes.ofInput x) (budget K k (d x.length * W x.length) x.length)
          (some (G x).flatten)) ∧
      IsConsistentMachine Rec f R Tr Sr (rejOracleClass Q) ∧
      (∀ O, rejOracleClass Q O → ∀ x : List Bool, (∀ z ∈ G x, O z = 0) →
        ComputesAt Rec f R Tr O x) ∧
      (∀ n : ℕ, Tr n ≤ budget K k (d n * W n) n) ∧
      (∀ n : ℕ, (Sr n : ℝ) ≤ K * ((W n : ℝ) ^ (1 - β) + (W n : ℝ) ^ β * Real.logb 2 (Q (m n))) *
        (Nat.log 2 (W n) + 1) ^ k) ∧
      (∀ n : ℕ, (Sr n : ℝ) ≤ K * ((W n : ℝ) ^ (1 - β) + (W n : ℝ) ^ (1 - ϵ + ϵ * β)) *
        (Nat.log 2 (W n) + 1) ^ k) ∧
      (∀ n : ℕ, R n ≤ K * (Nat.clog 2 (Q (m n)) + 1)) ∧
      (∀ O, rejOracleClass Q O → ∀ x w r : List Bool,
        ((Rec.queriesAsked ⟨x, r, w, O⟩).length : ℝ) ≤
          K * (d x.length + 1) * (W x.length : ℝ) ^ β) := by sorry

end TargetedSamplers
