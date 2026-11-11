-- Prove2me | Theorems.Thm_SoSPlantedCSP_Reduction_lemma_3_6
-- name    : SoSPlantedCSP.Reduction.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:40:52.247857+00:00
-- url     : https://prove2.me/theorems/e112784c-3a91-4233-abc3-9cc6eea6f55d
-- title:
--   Lemma 3.6 — sample splitting of one biased bit into $t$ bits of bias $s\varepsilon/2t$
-- statement:
--   Let $\mathrm{Bias}(\alpha)$ denote the law on $\{-1,1\}$ equal to $1$ with probability $(1+\alpha)/2$.
--
--   There are a randomized real-RAM program $S$ and a universal constant $C>0$ with the following properties. $S$ takes as input a bit $b\in\{-1,1\}$, a parameter $\hat\varepsilon\in(0,1)$ and $t\in\mathbb N$, and outputs bits $b_1,\dots,b_t\in\{-1,1\}$.
--
--   1. **Running time.** For every such input and every random tape, $S$ halts within $C\cdot2^t$ steps.
--   2. **Guarantee.** Let $s\in\{-1,1\}$ be a secret bit, $\varepsilon\in[0,1]$, and $b=sr$ with $r\sim\mathrm{Bias}(\varepsilon)$. Then the joint law of $(b_1,\dots,b_t)$, over $r$ and the tape, is $|\hat\varepsilon-\varepsilon|$-close in total variation to $t$ independent samples of $\mathrm{Bias}(s\varepsilon/2t)$: for every event $A\subseteq\{-1,1\}^t$,
--   $$\Pr\big[(b_1,\dots,b_t)\in A\big]\le\Pr_{y\sim\mathrm{Bias}(s\varepsilon/2t)^{\otimes t}}[y\in A]+|\hat\varepsilon-\varepsilon|.$$
--
--   From one sample $b_C=r_Cx^*_C$ of a planted constraint, the lemma produces $t$ nearly independent samples with planted sign $x^*_C$ and bias $\varepsilon/2t$, without knowing $x^*_C$. Applied to every constraint, it turns one instance from $\mathrm{XOR}(\mathcal H,x^*,\varepsilon)$ into $t$ instances that are close to independent draws from $\mathrm{XOR}(\mathcal H,x^*,\varepsilon/2t)$.
--
--   **Formalization Note** The paper writes $O(2^t)$; the Lean statement quantifies a universal constant $C$, chosen before every input. Total variation at most $\delta$ is stated as "every event has probability at most its target probability plus $\delta$", which is equivalent since applying it to complements gives the other inequality; tape probabilities are outer measures. At $t=0$ the output space is a single point and the target is the unique law on it.
--
--   Differences from the source:
--   - reading: ε unrestricted in the printed statement → ε ∈ [0,1]; reason: Bias(ε) is defined for ε ≥ 0 (Definition 2.1) and is a law only for ε ≤ 1; this contains every ε for which the statement makes sense
--   - encoding: an algorithm running in time O(2^t) → one randomized real-RAM program halting within ⌊C·2^t⌋ steps on every input and every tape, for a universal constant C > 0; reason: the paper names no machine model and leaves the O(·) constant universal
--   - encoding: |ε̂ − ε|-close in TV distance → for every event A ⊆ {−1,1}^t, Pr[output ∈ A] ≤ target(A) + |ε̂ − ε|, tape probability as outer measure; reason: the supremum over events of the probability difference is the total variation distance; the outer measure can only make the inequality harder
--   - encoding: the bit b, ε̂, t and the output bits → a fixed memory layout (cells 0–2) and output cells −1, …, −t decoded as 1 if positive and −1 otherwise; reason: a total decoding of a real-RAM memory; it changes no instance
-- source:
--   Arpon Basu, Andrew D. Lin, Peter Manohar, STOC 2027 submission #544 (October 2026), Lemma 3.6 (Sample splitting), p. 11 (PDF p. 13); restated with proof pp. 14–15 (PDF pp. 16–17)

import Mathlib
import Definitions.Def_SoSPlantedCSP_Reduction_Machine
import Definitions.Def_SoSPlantedCSP_Reduction_KXOR
import Definitions.Def_SoSPlantedCSP_Reduction_IO

namespace SoSPlantedCSP.Reduction

/-- Lemma 3.6 (sample splitting), Basu–Lin–Manohar, STOC 2027 submission #544, printed p. 11
(PDF p. 13), restated p. 14 (PDF p. 16). One randomized real-RAM program `S` and one constant
`C` such that, on input a bit `b`, `ε̂ ∈ (0,1)` and `t ∈ ℕ`, `S` halts within `C · 2^t` steps on
every tape; and if `b = s r` with `s ∈ {−1,1}` and `r ∼ Bias(ε)`, `0 ≤ ε ≤ 1`, the joint law of
the output `(b_1, …, b_t)` over `r` and the tape is `|ε̂ − ε|`-close in total variation to `t`
independent samples of `Bias(s ε / 2t)`, stated as: every event `A ⊆ {−1,1}^t` has probability at
most its target probability plus `|ε̂ − ε|`. -/
theorem lemma_3_6 :
    ∃ S : Program, ∃ C : ℝ, 0 < C ∧
      (∀ (b : ℤˣ) (εhat : ℝ) (t : ℕ), 0 < εhat → εhat < 1 →
        ∀ ω : Tape, HaltsWithin S (encSplit b εhat t) ω ⌊C * 2 ^ t⌋₊) ∧
      (∀ (s : ℤˣ) (ε εhat : ℝ) (t : ℕ), 0 < εhat → εhat < 1 → 0 ≤ ε → ε ≤ 1 →
        ∀ A : Set (Fin t → ℤˣ),
          jointProb (biasMass ε)
              (fun r ω => splitOut t (finalMem S (encSplit (s * r) εhat t) ω) ∈ A) ≤
            prob (iidMass (biasMass (((s : ℤ) : ℝ) * ε / (2 * (t : ℝ))))) (· ∈ A) +
              |εhat - ε|) := by sorry

end SoSPlantedCSP.Reduction
