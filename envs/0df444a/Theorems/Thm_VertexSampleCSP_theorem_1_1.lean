-- Prove2me | Theorems.Thm_VertexSampleCSP_theorem_1_1
-- name    : VertexSampleCSP.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:06.215207+00:00
-- url     : https://prove2.me/theorems/1acb17a6-66a4-4b17-8fad-796c1d48ecd1
-- title:
--   Theorem 1.1, p.2 — optimal vertex sampling: expected error $O_{r,q}(n^{r/2}\sqrt{m/k})$, and error $\varepsilon n^r$ w.p. $1-\delta$ from $O_{r,q}(\varepsilon^{-2}\log(2/\delta))$ variables
-- statement:
--   For every arity $r\ge2$ and every alphabet size $q\ge1$ there are constants $C,C'>0$ depending only on $r$ and $q$ such that the following holds for every $n$ and every instance $\mathcal I$ of arity $r$ over $[q]$ with $n$ variables, $m$ constraints and payoffs in $[0,1]$.
--
--   1. If $S$ is a uniformly random set of $k$ variables, $1\le k\le n$, then
--
--   $$\mathbb E\Big|\Big(\frac nk\Big)^r\mathrm{OPT}(\mathcal I[S])-\mathrm{OPT}(\mathcal I)\Big|\le C\,n^{r/2}\sqrt{\frac mk}.$$
--
--   2. If $0<\varepsilon,\delta<1$ and $k$ is any integer with $\min\{n,C'\varepsilon^{-2}\log(2/\delta)\}\le k\le n$, then, for a uniformly random set $S$ of $k$ variables, $|(n/k)^r\mathrm{OPT}(\mathcal I[S])-\mathrm{OPT}(\mathcal I)|\le\varepsilon n^r$ with probability at least $1-\delta$.
--
--   This is the sufficiency half of the statement that $\Theta(\varepsilon^{-2})$ variables are necessary and sufficient to estimate the optimum of a dense constraint satisfaction problem within $\varepsilon n^r$. It improves on the bound $O(\varepsilon^{-4}\log(1/\varepsilon))$ of Alon, Fernandez de la Vega, Kannan and Karpinski (2003).
--
--   Differences from the source:
--
--   - generalization: a sample of k = min{n, O_{r,q}(ε⁻²log(2/δ))} variables → every k with min{n, C′ε⁻²log(2/δ)} ≤ k ≤ n; reason: the single printed k = min{n, ⌈C′ε⁻²log(2/δ)⌉} is one such k, and Corollary D.2 proves the bound for every k above its threshold
--   - encoding: O_{r,q} → ∃ C > 0, ∃ C′ > 0 after r and q and before n, I, k, ε, δ; reason: the meaning of a constant depending only on r and q
--   - encoding: alphabet [q] = {1, …, q} → q ≥ 1 is a hypothesis and the alphabet is Fin q; reason: q = 0 leaves the optimum and the polytopes undefined, so this excludes only undefined cases
--   - encoding: I[S] is the instance on S → I.sub S on the subtype ↥S; reason: same instance, written in a type with |S| variables
--   - encoding: variables 1, …, n → Fin n; reason: same set up to the names of the variables
--   - encoding: E and probability over the random set → the finite averages unifAvg and unifProb over the k-subsets of Fin n; reason: same laws
--   - encoding: log → Real.log, the natural logarithm; reason: another base changes only C′
--   - encoding: an estimate within εn^r of OPT(I) → |(n/k)^r OPT(I[S]) − OPT(I)| ≤ εn^r; reason: the closed reading of "within", as in Corollary D.2
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Theorem 1.1, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_VertexSampleCSP_Instance
import Definitions.Def_VertexSampleCSP_OPT
import Definitions.Def_VertexSampleCSP_Instance_sub
import Definitions.Def_VertexSampleCSP_numConstraints
import Definitions.Def_VertexSampleCSP_PayoffsIn01
import Definitions.Def_VertexSampleCSP_unifAvg

namespace VertexSampleCSP

/-- **Theorem 1.1 (Optimal vertex sampling).** Chang, *Optimal Vertex Sampling for Constraint
Satisfaction Problems*, STOC 2027 submission (manuscript sha256 1e0edd23…), Theorem 1.1, p.2 (PDF
p.4): "Let I be an instance of arity r over [q] with n variables, m constraints, and payoffs in
[0, 1], and let S be a uniformly random set of k variables, 1 ≤ k ≤ n. Then
E|(n/k)^r OPT(I[S]) − OPT(I)| = O_{r,q}(n^{r/2} √(m/k)). Consequently, for 0 < ε, δ < 1, a sample of
k = min{n, O_{r,q}(ε^{−2} log(2/δ))} variables gives an estimate within εn^r of OPT(I) with probability
at least 1 − δ."

For every arity `r ≥ 2` and alphabet size `q ≥ 1` there are constants `C, C′ > 0`, depending on
`r` and `q` only, such that for every `n`, every instance `I` on the variables `{0, …, n − 1}` with
payoffs in `[0, 1]` and `m` constraints:
1. for every `1 ≤ k ≤ n` and a uniformly random `k`-subset `S`:
   `E|(n/k)^r OPT(I[S]) − OPT(I)| ≤ C n^{r/2} √(m/k)`;
2. for every `0 < ε, δ < 1` and every `k` with `min{n, C′ε^{−2} log(2/δ)} ≤ k ≤ n`:
   `P(|(n/k)^r OPT(I[S]) − OPT(I)| ≤ εn^r) ≥ 1 − δ`.

**Formalization Note.** `O_{r,q}` is rendered as an existential constant chosen after `r` and `q` and
before `n`, `I`, `k`, `ε`, `δ`. The sample-size clause is stated for every `k` from
`min{n, C′ε^{−2} log(2/δ)}` up to `n`, which contains the printed choice
`k = min{n, ⌈C′ε^{−2} log(2/δ)⌉}`. `log` is the natural logarithm (another base changes only `C′`).
`I[S]` is the instance on the subtype `↥S`. Expectations and probabilities are finite averages over
the `k`-subsets of `Fin n`. -/
theorem theorem_1_1 :
    ∀ r : ℕ, 2 ≤ r → ∀ q : ℕ, 1 ≤ q → ∃ C : ℝ, 0 < C ∧ ∃ C' : ℝ, 0 < C' ∧
      (∀ (n : ℕ) (I : Instance (Fin n) r q), PayoffsIn01 I → ∀ k : ℕ, 1 ≤ k → k ≤ n →
        unifAvg k (fun S => |((n : ℝ) / k) ^ r * OPT (I.sub S) - OPT I|) ≤
          C * (n : ℝ) ^ ((r : ℝ) / 2) * Real.sqrt ((numConstraints I : ℝ) / k)) ∧
      (∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        ∀ (n : ℕ) (I : Instance (Fin n) r q), PayoffsIn01 I → ∀ k : ℕ,
          min (n : ℝ) (C' * Real.log (2 / δ) / ε ^ 2) ≤ k → k ≤ n →
          1 - δ ≤ unifProb k (fun S =>
            |((n : ℝ) / k) ^ r * OPT (I.sub S) - OPT I| ≤ ε * (n : ℝ) ^ r)) := by sorry

end VertexSampleCSP
