-- Prove2me | Theorems.Thm_PairwiseRealize_Supplement_theorem_2_3
-- name    : PairwiseRealize.Supplement.theorem_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:27:02.180179+00:00
-- url     : https://prove2.me/theorems/8360cbfc-6203-4d44-9886-b99b930f7fba
-- title:
--   Theorem 2.3, p.5 — prescribed entries and extension: a shattered set of $\delta/8192$ positions depending only on $(n,\delta)$, $\log_2|\mathcal F(b)|\ge\delta/8192$, polynomial-time algorithms
-- statement:
--   **Prescribed entries and extension.** Let $V=\{0,1\}^n$, $N=2^n$, and for an integer target $b\in\mathbb Z^m$ let $y_V=2Tb-\sum_{x\in V}v_x$ be its centered target, $P_V=\sum_{x\in V}[-v_x,v_x]$ the full-cube zonotope and $\operatorname{depth}_V$ the Euclidean depth (2.4). There are an absolute constant $C_1>0$, a threshold $n_0$, a map $(n,\delta)\mapsto Q(n,\delta)\subseteq V$, a deterministic machine $M_1$, a randomized machine $M_2$ and constants $C',d$ such that, for every $n\ge n_0$ and every integer target $b$ with $y_V\in P_V$:
--
--   1. for every real $\delta$ with
--   $$\operatorname{depth}_V(y_V)\ \ge\ \delta\ \ge\ C_1n^2\log(n+1),$$
--   the set $Q(n,\delta)$ is shattered by the fiber $\mathcal F(b)$, and
--   $$|Q(n,\delta)|\ge\frac{\delta}{8192},\qquad \log_2|\mathcal F(b)|\ge\frac{\delta}{8192};$$
--   2. for every integer $\delta$ with the same promise, on input $(n,\delta,b)$ the machine $M_1$ has halted within $C'N^d$ steps with the membership table of $Q(n,\delta)$ on its tape;
--   3. for the same $\delta$ and every assignment $\alpha:Q(n,\delta)\to\{0,1\}$, on input $(n,\delta,b,\alpha)$ every halted run of $M_2$ shows the table of an exact extension of $\alpha$ (a member of $\mathcal F(b)$ agreeing with $\alpha$ on $Q(n,\delta)$), $M_2$ halts with probability one, and its expected number of steps is finite and at most $C'N^d$.
--
--   The set $Q(n,\delta)$ depends only on $n$ and $\delta$, so it works simultaneously for every target with that depth promise. The theorem turns depth into information: $\Omega(\delta)$ table entries can be prescribed arbitrarily and read back without error, and the fiber has at least $2^{\delta/8192}$ members.
--
--   **Formalization Note** The machines are the published randomized Post–Turing machine `OAI.MatchingFPRAS.RandomMachine`; "bit time" is its number of steps, a deterministic machine is one whose transition ignores the random bit, and the expected running time is the tail sum $\sum_t(1-\mathrm{haltMass}_t)$. The machines are constrained only on promise inputs.
--
--   Differences from the source:
--   - reading: "a deterministic algorithm constructs Q … the algorithm finds an exact extension" → two machines, a deterministic M₁ that outputs Q(n, δ) and a Las Vegas M₂ that receives (n, δ, b, α) and outputs an exact extension; reason: the extension algorithm is randomized (it calls Theorem 2.1's Las Vegas algorithm), and Q(n, δ) is recomputable from n and δ, so it need not be part of its input
--   - encoding: "deterministic … in polynomial bit time in N" → every run of length t ≥ C′(2ⁿ)^d has halted with the table of Q(n, δ); "expected polynomial bit time" → correct on every halted bit prefix, haltMass → 1, Σ_t (1 − haltMass t) summable and ≤ C′(2ⁿ)^d; reason: the published machine semantics; halted configurations are absorbing
--   - encoding: the inputs b, δ, α → n and δ in binary, the coordinates of b as signed binary numerals in the order featList n, α as the membership table of {x ∈ Q : α(x) = 1}; outputs are membership tables; reason: n is the binary logarithm of the table length and δ ≤ N under the promise, so no instance changes
--   - encoding: F ∈ F(b) a 0/1 function on V, α : Q → {0,1} → the set S = F⁻¹(1) ⊆ V, α a function on all rows of which only the values on Q are used; reason: the same objects
--   - encoding: log(n + 1), base unspecified → the natural logarithm; log₂ → Real.logb 2; reason: another base changes only C₁
-- source:
--   Shi, Sun, Robust Exact Realization of Pairwise Boolean Statistics, STOC 2027 submission (sha256 62090516…), Theorem 2.3, p.5 (PDF p.6), with "One may take c = 1/8192" (p.5); proof of Theorem 2.3, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_ContingencyTables
import Definitions.Def_PairwiseRealize_Model
import Definitions.Def_PairwiseRealize_Machine
import Definitions.Def_PairwiseRealize_Supplement_Fiber

namespace PairwiseRealize.Supplement

open OAI.MatchingFPRAS OAI.ContingencyTables.Algorithms

/-- **Theorem 2.3 (Prescribed entries and extension), p.5 (PDF p.6); proof p.14 (PDF p.15).**
K. Shi, H. Sun, *Robust Exact Realization of Pairwise Boolean Statistics*, STOC 2027 submission
(manuscript sha256 62090516…): "There are absolute constants C1, c > 0 such that, for sufficiently
large n, every integer target b ∈ ℤ^m whose centered target y = y_V lies in P_V and satisfies
depth_V(y) ≥ δ ≥ C1 n² log(n + 1), where depth is defined in (2.4), has a shattered set Q of size at
least cδ, and log₂ |F(b)| ≥ cδ. Given b and an integer promised lower bound δ, a deterministic
algorithm constructs Q in polynomial bit time in N. Given any assignment α : Q → {0, 1}, the
algorithm finds an exact extension in expected polynomial bit time in N. The set Q depends only on
n and the promised δ, and thus works simultaneously for every target with that depth promise."
"One may take c = 1/8192." (p.5); "|Q| ≥ εδ/2, so one may take c = 2⁻¹³" (p.14).

There are `C₁ > 0`, `n₀`, a map `Q(n, δ) ⊆ V` depending only on `n` and `δ`, a deterministic machine
`M₁`, a machine `M₂` and constants `C', d` such that for every `n ≥ n₀` and every integer target `b`
with `y_V ∈ P_V`:
1. for every real `δ` with `C₁n² log(n+1) ≤ δ ≤ depth_V(y_V)`: `Q(n, δ)` is shattered by `F(b)`,
   `|Q(n, δ)| ≥ δ/8192` and `log₂ |F(b)| ≥ δ/8192`;
2. for every natural `δ` with the same promise: on input `(n, δ, b)`, every run of `M₁` of at least
   `C'N^d` steps has halted with the membership table of `Q(n, δ)` on its tape (`N = 2ⁿ`);
3. for the same `δ` and every assignment `α`: on input `(n, δ, b, α|_Q)`, every halted run of `M₂`
   shows the table of an exact extension of `α` (a member of `F(b)` agreeing with `α` on `Q(n, δ)`),
   `M₂` halts with probability one, and its expected number of steps is finite and at most `C'N^d`.

**Formalization Note** `c = 1/8192` is the value the paper says may be taken. The machine model is
the published randomized Post–Turing machine `OAI.MatchingFPRAS.RandomMachine`; "bit time" is its
number of steps, a deterministic machine is one whose transition ignores the random bit, and
`haltMass M input t` is the probability that the run on `t` fair bits has halted, so the tail sum is
the expected running time. The machines are constrained only on promise inputs. `log` is the natural
logarithm (another base changes only `C₁`); `log₂` is `Real.logb 2`. The ball in the depth is
Euclidean (`depth`). -/
theorem theorem_2_3 :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ n₀ : ℕ, ∃ Q : (n : ℕ) → ℝ → Finset (Row n),
    ∃ (M₁ M₂ : RandomMachine) (C' d : ℕ), Deterministic M₁ ∧
      ∀ n ≥ n₀, ∀ b : Feat n → ℤ,
        centered n Finset.univ b ∈ zonotope n Finset.univ →
        (∀ δ : ℝ, C₁ * (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1) ≤ δ →
          δ ≤ depth n Finset.univ (centered n Finset.univ b) →
          IsShattered n b (Q n δ) ∧ δ / 8192 ≤ ((Q n δ).card : ℝ) ∧
            δ / 8192 ≤ Real.logb 2 ((fiber n b).card : ℝ)) ∧
        (∀ δ : ℕ, C₁ * (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1) ≤ (δ : ℝ) →
          (δ : ℝ) ≤ depth n Finset.univ (centered n Finset.univ b) →
          (∀ t : ℕ, C' * (2 ^ n) ^ d ≤ t → ∀ bits : Fin t → Bool,
            OutputsSet M₁ (promiseInput n δ b) bits n (Q n (δ : ℝ))) ∧
          ∀ α : Row n → Bool,
            (∀ (t : ℕ) (bits : Fin t → Bool),
              (run M₂ (extensionInput n δ b (Q n (δ : ℝ)) α) bits).state = none →
              ∃ S, IsExtension n b (Q n (δ : ℝ)) α S ∧
                OutputsSet M₂ (extensionInput n δ b (Q n (δ : ℝ)) α) bits n S) ∧
            Filter.Tendsto (haltMass M₂ (extensionInput n δ b (Q n (δ : ℝ)) α)) Filter.atTop
              (nhds 1) ∧
            Summable (fun t => 1 - haltMass M₂ (extensionInput n δ b (Q n (δ : ℝ)) α) t) ∧
            ∑' t, (1 - haltMass M₂ (extensionInput n δ b (Q n (δ : ℝ)) α) t) ≤
              (C' : ℝ) * ((2 : ℝ) ^ n) ^ d) := by sorry

end PairwiseRealize.Supplement
