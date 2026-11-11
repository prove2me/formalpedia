-- Prove2me | Theorems.Thm_RQCMoments_theorem_4_9
-- name    : RQCMoments.theorem_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:13:58.298946+00:00
-- url     : https://prove2.me/theorems/2c8b4511-45e6-46ce-b819-2ea289db422c
-- title:
--   Theorem 4.9 — design output probabilities are $O(\sqrt{N/(k(k+N))}+\varepsilon)$-close to Porter–Thomas in Kolmogorov distance
-- statement:
--   Let $N\ge 2$ and $k\ge 1$ be integers and $\varepsilon\le 1$. Let $\mu$ be any $\varepsilon$-approximate unitary $k$-design on $U(N)$, that is, a strong $\varepsilon$-approximate $(k,k)$-design with relative error (Definition 2.2, Remark 2.3). Fix basis indices $x,y$, let $\nu(k,\varepsilon)$ be the law of $X=|\langle x|U|y\rangle|^2$ for $U\sim\mu$, and let $\nu=\mathrm{Beta}(1,N-1)$, the law of the same quantity for a Haar random $U$. Then there is an absolute constant $C>0$, independent of $N,k,\varepsilon,\mu,x,y$, with
--   $$
--   d_K\big(\nu(k,\varepsilon),\nu\big)=\sup_{z\in\mathbb R}\big|F_{\nu(k,\varepsilon)}(z)-F_\nu(z)\big|\le C\left(\sqrt{\frac{N}{k(k+N)}}+\varepsilon\right).
--   $$
--
--   The statement says that approximate $k$-designs reproduce the Porter–Thomas distribution of output probabilities up to an error that decays like $1/\sqrt k$ for $k\ll N$ and like $\sqrt N/k$ for $k\gg N$, plus the design error.
--
--   **Formalization Note** The Kolmogorov bound is stated pointwise for every real $z$ with $F_{\nu(k,\varepsilon)}(z)=\mu\{U:|U_{xy}|^2\le z\}$ and $F_\nu(z)=\mathrm{Beta}(1,N-1)((-\infty,z])$; the constant $C$ is quantified before everything else.
--
--   Differences from the source:
--
--   - generalization: the entry |⟨0|U|0⟩|² (with the closing sentence: the same proof applies to any fixed entry |⟨x|U|y⟩|²) → every entry (x, y) : Fin N × Fin N; reason: the theorem's last sentence asserts the bound for every fixed entry; x = y = 0 is an instance
--   - encoding: d_K(ν(k,ε), ν) = sup_x |F_{ν(k,ε)}(x) − F_ν(x)| = O(√(N/(k(k+N))) + ε) → ∃ C > 0 chosen before N, the entry, k, ε, μ and z, with |μ{entry ≤ z} − Beta(1,N−1)(Iic z)| ≤ C(√(N/(k(k+N))) + ε) for all z ∈ ℝ; reason: an O(·) bound with an absolute constant on a supremum; same statement
--   - encoding: ν = Beta(1, N − 1) is the distribution of the same quantity for a Haar random U → first conjunct: (unitaryHaar N).map (entry x y) = Beta(1, N − 1); reason: the theorem asserts this identification; stating it as a conjunct keeps the clause and the explicit comparison law
--   - encoding: a probability distribution on U(N) → a Borel probability measure on the subtype Matrix.unitaryGroup (Fin N) ℂ (Borel σ-algebra of the subspace topology); reason: Lean representation of a distribution on the compact group U(N); same instances
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 4.9, (94), p.29 (PDF p.31)

import Mathlib
import Definitions.Def_RQCMoments_IsStrongDesign
import Definitions.Def_RQCMoments_entry
import Definitions.Def_RQCMoments_porterThomas

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

/-- **Theorem 4.9** (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 4.9, (94), p.29, PDF p.31).
For integers `N ≥ 2`, `k ≥ 1` and `ε ≤ 1`, let `μ` be any `ε`-approximate unitary `k`-design on
`U(N)` (a strong `(k,k)`-design with relative error, Remark 2.3), let `ν(k,ε)` be the law of
`X = |⟨x|U|y⟩|²` for `U ∼ μ`, and let `ν = Beta(1, N − 1)` be the law of the same quantity for a
Haar random `U`. Then `d_K(ν(k,ε), ν) = sup_z |F_{ν(k,ε)}(z) − F_ν(z)| = O(√(N/(k(k+N))) + ε)`.

**Formalization Note** The `O(·)` is an absolute constant `C > 0` chosen before `N`, the entry,
`k`, `ε`, `μ` and `z`; the supremum over `z` is a bound for every real `z`. The clause "ν is the
distribution of the same quantity for a Haar random U" is the first conjunct. The theorem is
stated for every entry `(x, y)` (the paper's last sentence: "The same proof applies to any fixed
entry"); the paper's displayed case is `x = y = 0`. `ε ≤ 1` has no lower bound, as printed. -/
theorem theorem_4_9 :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → ∀ x y : Fin N,
      (QAlgorithms.Schur.unitaryHaar N).map (entry x y) = porterThomas N ∧
      ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, ε ≤ 1 → ∀ μ : Measure (Matrix.unitaryGroup (Fin N) ℂ), IsStrongDesign μ k k ε →
        ∀ z : ℝ, |(μ {U | entry x y U ≤ z}).toReal - (porterThomas N (Set.Iic z)).toReal| ≤
          C * (Real.sqrt ((N : ℝ) / ((k : ℝ) * ((k : ℝ) + N))) + ε) := by sorry

end RQCMoments
