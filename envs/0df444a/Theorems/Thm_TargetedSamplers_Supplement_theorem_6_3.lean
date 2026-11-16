-- Prove2me | Theorems.Thm_TargetedSamplers_Supplement_theorem_6_3
-- name    : TargetedSamplers.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:15:57.527214+00:00
-- url     : https://prove2.me/theorems/d1e25bd7-a5f2-4e94-8b1a-77be288c81f9
-- title:
--   Theorem 6.3 — reconstructive generator from highly uniform circuits with low-degree gates
-- statement:
--   Let $T,w,d,k,\Delta:\mathbb N\to\mathbb N$ be computable in linear time, with $w(N)$ a power of $2$ and $w(N)T(N)\ge N$, and let $\epsilon\in(0,1)$ be a small enough constant. Let $\{C_N:\{0,1\}^N\to\{0,1\}^w\}$ be computable by a highly uniform family of $(d\times w)$-circuits with $(\Delta,T)$-low-degree gates of fan-in $k$. Then there are algorithms $\mathrm{Gen}$ (deterministic) and $\mathrm{Rec}$ (randomized, with oracle access) such that, for every $x\in\{0,1\}^N$:
--
--   1. **Somewhere generator.** $\mathrm{Gen}(x)$ runs in time $d\cdot\Delta^{3/\epsilon}\cdot w^{2+O(\epsilon)}\cdot\max\{\widetilde O(T),w\}$ and outputs $d'=O(d/\epsilon)$ lists $L(x)_1,\dots,L(x)_{d'}$ of $M$-bit strings, where $M=(\Delta^{1/\epsilon}w)^{\Omega(\epsilon^2)}$ and $|L(x)|\le d\cdot\Delta^{3/\epsilon}\cdot w^{2+O(\epsilon)}$.
--   2. **Reconstruction.** If $D:\{0,1\}^M\to\{0,1\}$ satisfies, for every $i\in[d']$,
--   $$\Big|\mathop{\mathbb E}_{y\sim\{0,1\}^M}[D(y)]-\mathop{\mathbb E}_{y\sim L(x)_i}[D(y)]\Big|\ge\frac1M,$$
--   then $\mathrm{Rec}^D(x)$ runs in time $(w+d)\cdot\mathrm{poly}(\Delta,w^\epsilon)\cdot\max\{k,\widetilde O(T)\}$, makes at most $(\Delta w^\epsilon)^c(w+dk)$ queries to $D$, and outputs $C_N(x)$ with probability at least $0.9$, where $c>1$ is a universal constant.
--
--   The generator is the engine of the targeted hitter of Theorem 6.9: any test that distinguishes every list lets $\mathrm{Rec}$ compute the hard function quickly.
--
--   **Formalization Note** One constant $K$ serves $O(d/\epsilon)$, $\Omega(\epsilon^2)$ (as $M\ge(\Delta^{1/\epsilon}w)^{\epsilon^2/K}$), $O(\epsilon)$ and $\mathrm{poly}(\Delta,w^\epsilon)=K(\Delta+1)^Kw^{K\epsilon}$; $\widetilde O(\cdot)$ is `budget`.
--
--   Differences from the source:
--   - encoding: ϵ small enough; universal c; O(·), Ω(·), poly(·) constants → c > 1 first; then the constants of Definition 6.1 (H); then one constant K and a threshold ϵ₀ > 0, all before T, w, d, k, Δ and the family; reason: the hidden constants of the hypothesis' Õ(T) printing time enter Gen's and Rec's running times
--   - encoding: computable in linear time → one program prints f(N) in binary from 1^N within budget(N); reason: linear up to the polylogarithmic gap between the log-cost RAM and a word RAM
--   - encoding: D : {0,1}^M → {0,1} → any oracle with values in {0,1} (values on other lengths arbitrary); Rec uses R(N) coins; time, query bound and success asserted for every D meeting the condition; reason: the oracle model of the base RAM
--   - encoding: |L(x)| → the total number of strings in the d′ lists; reason: L(x) is the multiset union of the lists
--   - encoding: M = (Δ^{1/ϵ} w)^{Ω(ϵ²)} → M ≥ (Δ^{1/ϵ} w)^{ϵ²/K} and M ≥ 1; reason: M ≥ 1 only excludes Δ = 0, where the printed bound is 0 and 1/M is undefined
--   - encoding: poly(Δ, w^ϵ) → K·(Δ+1)^K·w^{Kϵ}; reason: equivalent up to the constant; Δ + 1 avoids the value 0
--   - encoding: Definition 6.1 → IsHighlyUniformLDFamily: degree = total degree of the polynomial computed by G; fan-in = number of distinct children; fixed-width wiring formulas; reason: the definition fixes no encoding
--   - encoding: time bounds → the base mission's budget (constant and polylogarithmic factors); real powers rounded up; reason: the base mission's convention for the log-cost RAM
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Theorem 6.3, pp.47–48 (pdf pp.49–50)

import Mathlib
import Definitions.Def_TargetedSamplers_Supplement_LowDegreeCircuit
import Definitions.Def_TargetedSamplers_coinProb

namespace TargetedSamplers.Supplement

/-- Theorem 6.3 (reconstructive generator based on circuits with low-degree gates) (Chen, Doron,
Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission, manuscript sha256 599d0a59…, pp.47–48). Let
`T, w, d, k, ∆ : ℕ → ℕ` be computable in linear time, `w(N)` always a power of 2 and
`w(N) · T(N) ≥ N`, and let `ϵ ∈ (0, 1)` be a small enough constant. Let `{C_N : {0,1}^N → {0,1}^w}` be
computable by a highly uniform family of `(d × w)`-circuits with `(∆, T)`-low-degree gates of fan-in
`k`. Then there are algorithms `Gen, Rec` with:

* *(Somewhere generator.)* `Gen(x)`, `x ∈ {0,1}^N`, runs in time
  `d · ∆^{3/ϵ} · w^{2+O(ϵ)} · max{Õ(T), w}` and outputs `d′ = O(d/ϵ)` lists `L(x)_i` of `M`-bit
  strings, `M = (∆^{1/ϵ} · w)^{Ω(ϵ²)}`, with `|L(x)| ≤ d · ∆^{3/ϵ} · w^{2+O(ϵ)}`.
* *(Reconstruction.)* If `D : {0,1}^M → {0,1}` satisfies
  `|E_{y∼{0,1}^M}[D(y)] − E_{y∼L(x)_i}[D(y)]| ≥ 1/M` for every `i ∈ [d′]`, then `Rec^D(x)` runs in time
  `(w + d) · poly(∆, w^ϵ) · max{k, Õ(T)}`, makes at most `(∆ · w^ϵ)^c · (w + d · k)` queries to `D`,
  and outputs `C_N(x)` with probability at least `0.9`, where `c > 1` is a universal constant.

**Formalization Note** `c` is universal, chosen first. The constants hidden in Definition 6.1 (`H`)
are quantified next, then one constant `K` for all of `O(d/ϵ)`, `Ω(ϵ²)`, `O(ϵ)` and `poly(∆, w^ϵ)`
(which is `K · (∆ + 1)^K · w^{Kϵ}`), then the threshold `ϵ₀` of "`ϵ` small enough"; all are
independent of `T, w, d, k, ∆` and the family. `Õ(·)` and the outer factors are the base `budget`;
real quantities are rounded up. `|L(x)|` is the total number of strings in the lists. `D` is any
oracle with values in `{0,1}` (its values on strings of other lengths are arbitrary); `Rec` uses
`R(N)` random bits, and its time, query bound and success probability are asserted for every `D`
meeting the condition. `Gen` prints each list as its length followed by its strings. `M ≥ 1` is
stated (it only excludes `∆ = 0`, where the printed bound would be `0`). -/
theorem theorem_6_3 : ∃ c : ℝ, 1 < c ∧ ∀ H : UnifConsts, ∃ K : ℝ, 0 < K ∧ ∃ ϵ₀ : ℝ, 0 < ϵ₀ ∧
    ∀ ϵ : ℝ, 0 < ϵ → ϵ < 1 → ϵ < ϵ₀ →
    ∀ T w d k Δ : ℕ → ℕ, LinTimeComputable T → LinTimeComputable w → LinTimeComputable d →
      LinTimeComputable k → LinTimeComputable Δ →
      (∀ N, ∃ e : ℕ, w N = 2 ^ e) → (∀ N, N ≤ w N * T N) →
    ∀ C : List Bool → List Bool, IsHighlyUniformLDFamily H id C d w k (fun N => (Δ N : ℝ)) T →
    ∃ (d' M R : ℕ → ℕ) (Ls : List Bool → List (List (List Bool))) (Gen Rec : Program) (Kb kb : ℕ),
      (∀ N, (d' N : ℝ) ≤ K * d N / ϵ) ∧
      (∀ N, 1 ≤ M N ∧ (((Δ N : ℝ) ^ (1 / ϵ) * w N) ^ (ϵ ^ 2 / K) ≤ M N)) ∧
      (∀ x : List Bool,
        (Ls x).length = d' x.length ∧ (∀ l ∈ Ls x, ∀ y ∈ l, y.length = M x.length) ∧
        ((((Ls x).map List.length).sum : ℕ) : ℝ) ≤
          d x.length * (Δ x.length : ℝ) ^ (3 / ϵ) * (w x.length : ℝ) ^ (2 + K * ϵ)) ∧
      (∀ x : List Bool,
        Gen.RunsIn (Tapes.ofInput x)
          (budget Kb kb ⌈d x.length * (Δ x.length : ℝ) ^ (3 / ϵ) * (w x.length : ℝ) ^ (2 + K * ϵ) *
            (max (T x.length) (w x.length) : ℕ)⌉₊ x.length)
          (some ((Ls x).flatMap fun l => encNat l.length ++ l.flatten))) ∧
      (∀ (x : List Bool) (O : List Bool → ℕ), (∀ s, O s ≤ 1) →
        (∀ i : ℕ, i < d' x.length →
          1 / (M x.length : ℝ) ≤
            |coinProb (M x.length) (fun y => O y = 1) -
              (((Ls x).getD i []).countP (fun y => decide (O y = 1)) : ℝ) /
                ((Ls x).getD i []).length|) →
        (∀ ρ : List Bool, ρ.length = R x.length →
          (∃ v, Rec.RunsIn ⟨x, ρ, [], O⟩
            (budget Kb kb ⌈((w x.length + d x.length : ℕ) : ℝ) * ((Δ x.length : ℝ) + 1) ^ K *
              (w x.length : ℝ) ^ (K * ϵ) * (max (k x.length) (T x.length) : ℕ)⌉₊ x.length) v) ∧
          ((Rec.queriesAsked ⟨x, ρ, [], O⟩).length : ℝ) ≤
            ((Δ x.length : ℝ) * (w x.length : ℝ) ^ ϵ) ^ c *
              (w x.length + d x.length * k x.length : ℕ)) ∧
        (9 / 10 : ℝ) ≤ coinProb (R x.length) (fun ρ => Rec.Outputs ⟨x, ρ, [], O⟩ (some (C x)))) := by sorry

end TargetedSamplers.Supplement
