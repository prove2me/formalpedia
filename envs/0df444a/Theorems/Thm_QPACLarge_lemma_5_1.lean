-- Prove2me | Theorems.Thm_QPACLarge_lemma_5_1
-- name    : QPACLarge.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:06:47.572185+00:00
-- url     : https://prove2.me/theorems/a6244965-4355-4661-a5aa-e6692eb8c11f
-- title:
--   Lemma 5.1 — padded query lower bound $\mathbb E_g\Pr[\text{agreement}\ge1/2+\gamma]\le M/(2M\gamma-q)^2$
-- statement:
--   Let $1 \le m < n$, $M = 2^m$, and consider the padded class $D_{n,m} = \{f_g(x, z) = g(x) : g \in \mathrm{ALL}_m\}$, $(x,z) \in \{0,1\}^m \times \{0,1\}^{n-m}$. Suppose a randomized classical learner $A$ makes at most $q$ membership queries and outputs a hypothesis $h$ on $n$ bits. Then for every $\gamma > q/(2M)$,
--
--   $$
--   \mathbb E_{g \sim \mathrm{ALL}_m}\Big[\Pr_A\Big[\Pr_{x,z}[h(x,z) = g(x)] \ge \frac12 + \gamma\Big]\Big] \le \frac{M}{(2M\gamma - q)^2}.
--   $$
--
--   The average is over all $2^M$ functions $g$. This second-moment version of the transcript argument (Theorem 4.1) is the classical lower bound behind Theorem 1.5.
--
--   Differences from the source:
--   - generalization: a randomized classical learner making at most $q$ membership queries and outputting a deterministic Boolean circuit $h$ → any probability distribution over decision trees with at most $q$ queries on every path and any hypothesis $h : \{0,1\}^n \to \{0,1\}$ at the leaves; reason: a learner with fixed coins is such a tree and a circuit determines its function; the proof uses only that $h$ is fixed given the transcript
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Lemma 5.1, p.34

import Mathlib
import Definitions.Def_QPACLarge_treeSuccess
import Definitions.Def_QPACLarge_padFn
import Definitions.Def_QPACLarge_agreement

namespace QPACLarge

open QAlgorithms

/-- **Lemma 5.1 (Padded Query Lower Bound).**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Lemma 5.1, p.34: "Let `1 ≤ m < n`, write `M = 2^m`, and consider the target class
`D_{n,m} = {f_g(x, z) = g(x) : g ∈ ALL_m}`, where `(x, z) ∈ {0,1}^m × {0,1}^{n−m}`. Suppose a
randomized classical learner makes at most `q` membership queries and outputs a deterministic
Boolean circuit `h` on `n` bits. Then, for every `γ > q/(2M)`,
`E_{g∼ALL_m}[Pr_A[Pr_{x,z}[h(x, z) = g(x)] ≥ 1/2 + γ]] ≤ M/(2Mγ − q)²`."

**Formalization Note.** The learner is any randomized decision tree over the `n`-bit inputs with at
most `q` queries on every path and any hypothesis `h : {0,1}ⁿ → {0,1}` at its leaves (the published
`RandDecisionTree`, `RandMakesAtMost`). `Pr_{x,z}[h(x,z) = g(x)]` is `agreement(f_g, h)`; the average
over `g` is uniform over the `2^M` functions. -/
theorem lemma_5_1 (n m q : ℕ) (hm : 1 ≤ m) (hmn : m < n)
    (R : RandDecisionTree (Qubits n) Bool (Qubits n → Bool)) (hR : RandMakesAtMost R q)
    (γ : ℝ) (hγ : (q : ℝ) / (2 * 2 ^ m) < γ) :
    ((2 : ℝ) ^ (2 ^ m))⁻¹ * ∑ g : Qubits m → Bool,
        treeSuccess R (padFn n g) (fun h => 1 / 2 + γ ≤ agreement (padFn n g) h) ≤
      (2 : ℝ) ^ m / (2 * 2 ^ m * γ - q) ^ 2 := by sorry

end QPACLarge
