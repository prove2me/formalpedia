-- Prove2me | Theorems.Thm_UniversalNonstochastic_Main_Supplement_lemma_21
-- name    : UniversalNonstochastic.Main.Supplement.lemma_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:32:04.445533+00:00
-- url     : https://prove2.me/theorems/bae000da-5c0c-4fbb-a306-d909102336d0
-- title:
--   Lemma 21 — computable probability measures with simple numbers have light, simple tails
-- statement:
--   Fix a Gödel numbering of the algorithms from $\mathcal X\times\mathbb N$ to the rationals. There is a constant $c_{31}$ such that for all $\alpha,n\in\mathbb N_0$: if a probability measure $P$ on $\mathcal X$ has a number $\pi$ with $K(\pi)\le\alpha$, then there is $N\in\mathbb N$ with
--   $$P(\mathcal X\setminus[N])<2^{-\alpha-n}\qquad\text{and}\qquad K(N)\le\alpha+K(n)+c_{31}.$$
--
--   Here $[N]=\{1,\dots,N\}$. The parameter $n$ trades lightness of the tail for simplicity of $N$; the lemma supports Theorem 9.
--
--   **Formalization Note** $P(\mathcal X\setminus[N])$ is the sum of $P(\{\omega\})$ over $\omega>N$; the complexity bound is an inequality in $\mathbb N\cup\{\infty\}$.
--
--   Differences from the source:
--   - encoding: a fixed Gödel numbering of the algorithms from X × N to rational numbers → an arbitrary GodelNumbering parameter (acceptable numbering with positive indices, rational-name outputs), quantified before the constants; reason: the source's Gödel numberings are acceptable numberings; the statement holds for every one
--   - reading: outputs a rational number within 2^(−n) of P({ω}) → |P({ω}) − q| ≤ 2^(−n); reason: 'within' can be read with ≤ or <; ≤ admits more numbers π, which is the stronger reading for this statement
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, Lemma 21, p.21 (PDF p.21); numbering and numbers defined on p.9

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_Complexity
import Definitions.Def_UniversalNonstochastic_Main_Supplement_Complexities
import Definitions.Def_UniversalNonstochastic_Main_Supplement_ComputableModels

namespace UniversalNonstochastic.Main.Supplement

/-- Lemma 21, p.21: for the fixed Gödel numbering `G` there is a constant `c₃₁` such that for
all `α, n ∈ ℕ₀`: if a probability measure `P` on `𝓧` has a number `π` with `K(π) ≤ α`, there is
`N ∈ ℕ` with `P(𝓧 ∖ [N]) < 2^{-α-n}` and `K(N) ≤ α + K(n) + c₃₁`. -/
theorem lemma_21 (U : OptimalPrefixDecoder) (G : GodelNumbering) :
    ∃ c₃₁ : ℕ, ∀ (α n : ℕ) (P : ℕ+ → ℝ) (π : ℕ+),
      IsProbabilityOn P → IsNumberOf G π P → KNat U π ≤ (α : ℕ∞) →
        ∃ N : ℕ+, ∑' ω : ℕ+, {ω : ℕ+ | N < ω}.indicator P ω < (2 : ℝ) ^ (-(α : ℝ) - n) ∧
          Kobj U N ≤ (α : ℕ∞) + KNat U n + c₃₁ := by sorry

end UniversalNonstochastic.Main.Supplement
