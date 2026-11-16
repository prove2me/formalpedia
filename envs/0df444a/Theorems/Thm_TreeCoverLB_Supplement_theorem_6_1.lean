-- Prove2me | Theorems.Thm_TreeCoverLB_Supplement_theorem_6_1
-- name    : TreeCoverLB.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:23:19.651535+00:00
-- url     : https://prove2.me/theorems/a9f77fcb-8703-4c6a-beda-d3cce49a851f
-- title:
--   Theorem 6.1 — $\mathrm{ind}_{\mathbb Z_p}(|I_{p,k}|)\ge 4^m+k-3^m-1$ with $m=\lfloor\log_3k\rfloor$, hence $\Omega(k^{\log_34})$
-- statement:
--   Let $p$ be a prime and let $k\ge 3$ be an integer. Put $m=\lfloor\log_3 k\rfloor$ and $R(k)=4^m+k-3^m$. Then the $(p,k)$-agreement index, the topological index of the agreement complex $|I_{p,k}|$ under the diagonal $\mathbb Z_p$-action, satisfies
--   $$
--   \operatorname{ind}_{\mathbb Z_p}(|I_{p,k}|)\ \ge\ R(k)-1 .
--   $$
--   Consequently $\operatorname{ind}_{\mathbb Z_p}(|I_{p,k}|)=\Omega(k^{\log_3 4})$. More precisely, there is an absolute constant $c>0$ such that for every prime $p$ and every $k\ge 3$,
--   $$
--   \operatorname{ind}_{\mathbb Z_p}(|I_{p,k}|)\ \ge\ c\,k^{\log_3 4}.
--   $$
--   Here $\operatorname{ind}_{\mathbb Z_p}(X)$ is the least $d\ge 0$ for which a continuous $\mathbb Z_p$-equivariant map $X\to|E_d\mathbb Z_p|$ exists, and $+\infty$ if there is none (Definition 4.2).
--
--   Through Theorem 4.3 an upper bound $d$ on this index gives a tree-cover distortion lower bound $\Omega(n^{1/(d+1)})$. This theorem shows that the topological method of §4 cannot give an exponent better than $1/(R(k))$, which is $O(1/k^{\log_3 4})$. For $k=3$ the bound $R(3)-1=3$ matches the upper bound $(k-1)^2-1=3$ of Theorem 5.1 for every prime $p\ge 2$.
--
--   **Formalization Note** "$\operatorname{ind}\ge N$" is stated as: every $d$ that admits a map $\psi$ with `IsAgreementIndexMap p k d ψ` satisfies $N\le d$. In Lean $m$ is `Nat.log 3 k`, the floor of $\log_3 k$. The natural-number subtractions are exact because $3^m\le k$ and $R(k)\ge 4^m\ge 1$. The power $k^{\log_3 4}$ is the real power `(k : ℝ) ^ (Real.log 4 / Real.log 3)`.
--
--   Differences from the source:
--   - encoding: ind_{ℤ_p}(|I_{p,k}|) ≥ N → every d admitting a continuous ℤ_p-equivariant map |I_{p,k}| → |E_dℤ_p| satisfies N ≤ d; reason: the index is the infimum of those d (+∞ when there is none), so the two say the same
--   - encoding: m = ⌊log_3 k⌋, R(k) = 4^m + k − 3^m → Nat.log 3 k and ℕ arithmetic 4^m + k − 3^m − 1; reason: Nat.log is the floor logarithm, and the subtractions are exact since 3^m ≤ k and R(k) ≥ 1
--   - reading: ind_{ℤ_p}(|I_{p,k}|) = Ω(k^{log_3 4}) → ∃ c > 0, for every prime p and every k ≥ 3, c·k^{log 4/log 3} ≤ d for every admissible d; reason: the strongest reading of Ω (one constant, uniform in p, no threshold beyond k ≥ 3); the proof (p.29) gives c = 3/16 for every p and k ≥ 3
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), Theorem 6.1, p.23 (PDF p.25); constant 3/16 in the proof of Theorem 6.1, p.29 (PDF p.31)

import Mathlib
import Definitions.Def_TreeCoverLB_realization
import Definitions.Def_TreeCoverLB_EJoin
import Definitions.Def_TreeCoverLB_agreementComplex
import Definitions.Def_TreeCoverLB_IsAgreementIndexMap

open Classical

namespace TreeCoverLB.Supplement

/-- **Theorem 6.1** (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*,
arXiv:2607.27264 (version of October 31, 2026), Theorem 6.1, p.23 (PDF p.25)): let `p` be a prime
and `k ≥ 3`; with `m = ⌊log₃ k⌋` and `R(k) = 4^m + k − 3^m`,
`ind_{ℤ_p}(|I_{p,k}|) ≥ R(k) − 1`. Consequently `ind_{ℤ_p}(|I_{p,k}|) = Ω(k^{log₃ 4})`.

**Formalization Note** `ind_{ℤ_p}(|I_{p,k}|)` (Definition 4.2) is the infimum of the `d` admitting
a continuous `ℤ_p`-equivariant map `|I_{p,k}| → |E_dℤ_p|` (`+∞` if there is none); a lower bound
`ind ≥ N` is stated as: every `d` admitting such a map (`IsAgreementIndexMap p k d ψ`) satisfies
`N ≤ d`. `m = Nat.log 3 k` (the floor of `log₃ k`); the natural-number subtractions are exact since
`3^m ≤ k` and `R(k) ≥ 1`. The `Ω` clause is stated with one constant `c > 0` uniform over all primes
`p` and all `k ≥ 3`, and `k^{log₃ 4}` is the real power `k ^ (log 4 / log 3)`. -/
theorem theorem_6_1 :
    (∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 3 ≤ k →
      ∀ (d : ℕ) (ψ : ((Fin k → ZMod p) → ℝ) → (Fin (d + 1) × ZMod p → ℝ)),
        IsAgreementIndexMap p k d ψ →
          4 ^ Nat.log 3 k + k - 3 ^ Nat.log 3 k - 1 ≤ d) ∧
    ∃ c : ℝ, 0 < c ∧
      ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 3 ≤ k →
        ∀ (d : ℕ) (ψ : ((Fin k → ZMod p) → ℝ) → (Fin (d + 1) × ZMod p → ℝ)),
          IsAgreementIndexMap p k d ψ →
            c * (k : ℝ) ^ (Real.log 4 / Real.log 3) ≤ (d : ℝ) := by sorry

end TreeCoverLB.Supplement
