-- Prove2me | Theorems.Thm_UniversalNonstochastic_Main_eq_32
-- name    : UniversalNonstochastic.Main.eq_32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:05:16.338208+00:00
-- url     : https://prove2.me/theorems/4d164c69-61b1-4ffb-a535-794740c6e92a
-- title:
--   Section A.2, equation (32) — plain versus prefix randomness deficiency in a finite set
-- statement:
--   Let $C$ and $K$ be plain and prefix complexity, given by optimal plain and prefix decoders. There are constants $c_9$ and $c_{10}$ such that, for all finite sets $\Omega\subseteq\mathbb N$ and all $\omega\in\Omega$,
--   $$\log|\Omega|-C(\omega)\;\le\;\log|\Omega|-C(\omega\mid\Omega)+c_9\;\le\;2\bigl(\log|\Omega|-K(\omega\mid\Omega)\bigr)+c_{10}. \tag{32}$$
--   The logarithm is binary. The factor $2$ multiplies the whole prefix randomness deficiency $\log|\Omega|-K(\omega\mid\Omega)$.
--
--   Both constants are uniform in $\Omega$ and $\omega$, and there is no bound on $|\Omega|$. In the source this chain gives $d_C\le 2d_e^{\rm set}+O(1)$, which allows Theorem 10 to be applied with $F=C$ for the lower bound of Theorem 1. The source attributes it to [19, Proposition 17] and [12, Proposition 1].
--
--   **Formalization Note** The chain is evaluated in the extended reals; all complexities are finite (optimality), so this is ordinary real arithmetic. The constants are required to be positive, following the convention for the numbered constants $c_1,c_2,\dots$ of Appendix A (p.15); since enlarging $c_9$ and then $c_{10}$ preserves the chain, this is equivalent to their mere existence.
--
--   Differences from the source:
--   - encoding: objects ω in a basic space 𝓧 in computable bijection with ℕ → objects are positive integers ℕ+ (the paper’s ℕ = {1,2,…}), coded by themselves; reason: the source explicitly permits replacing 𝓧 by ℕ in every formal statement (p.4); ObjectEncoding and the transport functions implement its fixed computable bijection without changing any instance
--   - encoding: K, C: prefix and plain complexity defined by fixed optimal decoders → U, V: arbitrary optimal conditional prefix/plain decoders (structures), complexity = minimal halting-program length in ℕ∞, unconditional = condition 0; reason: the source fixes any optimal decoders; ℕ∞ is the exact infimum (⊤ only on no description, which optimality excludes); every statement is quantified over all such choices before its constants
--   - encoding: constants c9, c10 → c₉ c₁₀ : ℝ with 0 < c₉ and 0 < c₁₀; reason: Appendix A (p.15) declares the numbered constants positive; enlarging c₉ and then c₁₀ preserves both inequalities, so existence of positive constants is equivalent to existence of any
--   - encoding: real-valued differences of complexities → EReal arithmetic on complexities coerced from ℕ∞; reason: complexities are finite by optimality, so EReal subtraction agrees with real subtraction
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/11.pdf, Sect. A.2, eq. (32), p.17 (PDF p.17)

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_Complexity

namespace UniversalNonstochastic.Main

/-- Section A.2, equation (32), p.17: for some constants `c₉, c₁₀`, for every finite set
`Ω ⊆ 𝓧` and every `ω ∈ Ω`,
`log|Ω| - C(ω) ≤ log|Ω| - C(ω | Ω) + c₉ ≤ 2 (log|Ω| - K(ω | Ω)) + c₁₀`. -/
theorem eq_32 (V : OptimalPlainDecoder) (U : OptimalPrefixDecoder) :
    ∃ c₉ c₁₀ : ℝ, 0 < c₉ ∧ 0 < c₁₀ ∧ ∀ (Ω : Finset ℕ+), ∀ ω ∈ Ω,
      ((Real.logb 2 (Ω.card : ℝ) : ℝ) : EReal) - toEReal (Cobj V ω) ≤
          ((Real.logb 2 (Ω.card : ℝ) : ℝ) : EReal) - toEReal (CobjGivenSet V ω Ω) +
            ((c₉ : ℝ) : EReal) ∧
        ((Real.logb 2 (Ω.card : ℝ) : ℝ) : EReal) - toEReal (CobjGivenSet V ω Ω) +
            ((c₉ : ℝ) : EReal) ≤
          2 * (((Real.logb 2 (Ω.card : ℝ) : ℝ) : EReal) - toEReal (KobjGivenSet U ω Ω)) +
            ((c₁₀ : ℝ) : EReal) := by sorry

end UniversalNonstochastic.Main
