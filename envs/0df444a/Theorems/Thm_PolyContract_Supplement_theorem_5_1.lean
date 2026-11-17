-- Prove2me | Theorems.Thm_PolyContract_Supplement_theorem_5_1
-- name    : PolyContract.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:03:17.99851+00:00
-- url     : https://prove2.me/theorems/de93d60e-8697-4189-95de-a06734727ae8
-- title:
--   Theorem 5.1 — $\lceil 2\varepsilon^{-1}\ln(1/(1-\bar\alpha))\rceil+1$ best-response queries give a $(1-\varepsilon)$-optimal contract
-- statement:
--   Consider any contract instance over an action set $K\subseteq\mathbb R^E_{\ge0}$ with rewards $m\ge0$ and cost $c\ge0$, $c(0)=0$, in which best responses exist on $[0,1]$ and the reward attains its maximum over them (ties broken in favour of the principal). Let $\mathrm{OPT}:=\sup_{\alpha\in[0,1]}U_P(\alpha)$.
--
--   There is an absolute constant $C$ such that for every $\varepsilon\in(0,1)$ and $\bar\alpha\in[0,1)$ there is a set $Q\subseteq[0,1]$ of at most
--   $$\Big\lceil \frac{2}{\varepsilon}\ln\frac{1}{1-\bar\alpha}\Big\rceil+1$$
--   shares, each a rational with at most $\lceil C(1+\log_2(1/\varepsilon)+\log_2(1/(1-\bar\alpha)))\rceil$ bits, such that for every such instance for which $\bar\alpha$ is a share bound some $q\in Q$ has $U_P(q)\ge(1-\varepsilon)\,\mathrm{OPT}$.
--
--   So, given an exact best-response oracle and a share bound, querying the shares of $Q$ and returning the best one finds a $(1-\varepsilon)$-optimal contract.
--
--   Differences from the source:
--   - generalization: a (1 − ε)-optimal contract can be found with at most ⌈2ε⁻¹ ln(1/(1 − ᾱ))⌉ + 1 oracle calls → a set Q of at most that many shares, depending only on (ε, ᾱ), contains a (1 − ε)-optimal contract of every instance with share bound ᾱ; reason: the proof's scheme is non-adaptive; querying Q and returning the best share is an algorithm with that many calls, so the statement implies the source's
--   - generalization: the action sets of §5 (in particular compact convex K containing zero) → any K ⊆ ℝ^E_{≥0} satisfying the attainment assumption of §2; reason: the theorem presupposes only an exact best-response oracle; compact convex K with continuous c satisfies the assumption
--   - encoding: O(1 + log(1/ε) + log(1/(1 − ᾱ))) bits → at most ⌈C(1 + log₂(1/ε) + log₂(1/(1 − ᾱ)))⌉ bits with one absolute C, numerator and denominator below 2^bits; reason: the usual reading of an O-bound; base-2 logarithms change only the constant
--   - encoding: OPT := sup_{α∈[0,1]} U_P(α) → real sSup of the utilities on [0, 1]; reason: the utilities are bounded on [0, 1] under the attainment assumption
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Theorem 5.1, p.11 (PDF p.12); restated with proof pp.76–77 (PDF pp.77–78)

import Mathlib
import Definitions.Def_PolyContract_BitLength
import Definitions.Def_PolyContract_Supplement_GenContract

set_option autoImplicit false

namespace PolyContract.Supplement

/-- **Theorem 5.1** (Klimm, Lippke, Warode, arXiv:2611.04934, version of November 3, 2026, sha256
18cfc0a5…, p.11; restated with proof pp.76–77): given an exact best-response oracle, a share bound
`ᾱ ∈ [0, 1)` and `ε ∈ (0, 1)`, a `(1 − ε)`-optimal contract can be found with at most
`⌈2ε⁻¹ ln(1/(1 − ᾱ))⌉ + 1` oracle calls, at rational shares with
`O(1 + log(1/ε) + log(1/(1 − ᾱ)))` bits.

**Formalization Note** The scheme of the proof is non-adaptive, and it is stated in that form: for
every `ε` and `ᾱ` there is a set `Q ⊆ [0, 1]` of at most `⌈2ε⁻¹ ln(1/(1 − ᾱ))⌉ + 1` shares, chosen
from `(ε, ᾱ)` alone, each a rational of at most `⌈C(1 + log₂(1/ε) + log₂(1/(1 − ᾱ)))⌉` bits for one
absolute `C`, such that for every instance over any action set that satisfies the attainment
assumption of §2 and has the share bound `ᾱ`, some queried share has utility at least
`(1 − ε) OPT`; the algorithm queries `Q` and returns the best share. The logarithm in the count is
natural. -/
theorem theorem_5_1 : ∃ C : ℕ, ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ ᾱ : ℝ, ᾱ ∈ Set.Ico (0 : ℝ) 1 →
    ∃ Q : Finset ℝ, (Q.card : ℤ) ≤ ⌈2 / ε * Real.log (1 / (1 - ᾱ))⌉ + 1 ∧
      (∀ q ∈ Q, q ∈ Set.Icc (0 : ℝ) 1 ∧
        HasBitLength ⌈(C : ℝ) * (1 + Real.logb 2 (1 / ε) + Real.logb 2 (1 / (1 - ᾱ)))⌉₊ q) ∧
      ∀ {ι : Type} [Fintype ι] (I : GenContract ι), I.Valid → I.Attains → I.IsShareBound ᾱ →
        ∃ q ∈ Q, (1 - ε) * I.OPT ≤ I.principalUtility q := by sorry

end PolyContract.Supplement
