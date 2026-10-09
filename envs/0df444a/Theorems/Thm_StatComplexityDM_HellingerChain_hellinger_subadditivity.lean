-- Prove2me | Theorems.Thm_StatComplexityDM_HellingerChain_hellinger_subadditivity
-- name    : StatComplexityDM.HellingerChain.hellinger_subadditivity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:22:33.980006+00:00
-- url     : https://prove2.me/theorems/504abd6d-8d9d-4538-bc49-2aeda291e6db
-- title:
--   Lemma A.13 (97), p. 73 — D²_H(P,Q) ≤ 10² log(n)·E_P[Σᵢ D²_H(P⁽ⁱ⁾(·|X₁:ᵢ₋₁), Q⁽ⁱ⁾(·|X₁:ᵢ₋₁))] for n ≥ 2
-- statement:
--   This is the subadditivity of squared Hellinger distance for sequential laws (Lemma A.13, (97)).
--
--   Let $n \ge 2$ and let $\mathcal X_1, \dots, \mathcal X_n$ be finite sets. For each $i$, let $P^{(i)}(\cdot \mid \cdot)$ and $Q^{(i)}(\cdot \mid \cdot)$ be probability kernels from $\mathcal X^{(i-1)} = \prod_{t=1}^{i-1}\mathcal X_t$ to $\mathcal X_i$. Let $\mathbb P$ and $\mathbb Q$ be the laws of $X_1, \dots, X_n$ under $X_i \sim P^{(i)}(\cdot \mid X_{1:i-1})$ and $X_i \sim Q^{(i)}(\cdot \mid X_{1:i-1})$ respectively. Then
--   $$
--   D^2_{\mathrm H}(\mathbb P, \mathbb Q) \le 10^2 \log(n) \cdot \mathbb E_{\mathbb P}\Big[\sum_{i=1}^n D^2_{\mathrm H}\big(P^{(i)}(\cdot \mid X_{1:i-1}), Q^{(i)}(\cdot \mid X_{1:i-1})\big)\Big],
--   $$
--   where $D^2_{\mathrm H}(p, q) = \sum_a(\sqrt{p(a)} - \sqrt{q(a)})^2$ and $\log$ is the natural logarithm.
--
--   The inequality decomposes the distance between two joint laws into the expected distances between their conditional laws, losing only a logarithmic factor in the length $n$. In the paper it turns the per-round Hellinger estimation error into a bound on the distance between the laws of whole interaction histories, which is the step behind the regret lower bound (Theorem 3.2).
--
--   **Formalization Note** Finite alphabets: laws are probability vectors and expectations finite sums. The hypothesis $n \ge 2$ is added: the paper states (97) for every $n$, but for $n = 1$ the right side is $0$ (since $\log 1 = 0$) while $D^2_{\mathrm H}(P^{(1)}, Q^{(1)}) > 0$ whenever $P^{(1)} \ne Q^{(1)}$, and the proof's final step $2(6\log(96n) + \frac{18}{96n}) \le 10^2\log(n)$ holds only for $n \ge 2$. Kernels are functions of the whole sequence that depend only on the prefix (`IsSeqKernel`).
-- source:
--   arXiv:2112.13487v3, App. A.2, Lemma A.13, (97), p. 73 (proof pp. 73–74)

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_StatComplexityDM_HellingerChain_SeqLaw

namespace StatComplexityDM.HellingerChain

open FoundationsRL.GeneralDM

/-- Lemma A.13, (97) (arXiv:2112.13487v3, p. 73), finite alphabets, for `n ≥ 2`: if `P`, `Q`
are the laws of `X_1, …, X_n` under the sequential kernels `P^{(i)}`, `Q^{(i)}`, then
`D²_H(P, Q) ≤ 10² log(n) · E_P[Σ_i D²_H(P^{(i)}(· | X_{1:i−1}), Q^{(i)}(· | X_{1:i−1}))]`.
The page states (97) for every `n`; at `n = 1` its right side is `0` and the claim fails, and
the proof's last step `2(6 log(96n) + 18/(96n)) ≤ 10² log(n)` needs `n ≥ 2`. -/
theorem hellinger_subadditivity {n : ℕ} {X : Fin n → Type*} [∀ i, Fintype (X i)]
    [∀ i, DecidableEq (X i)]
    (P Q : (i : Fin n) → ((j : Fin n) → X j) → X i → ℝ)
    (hP : IsSeqKernel P) (hQ : IsSeqKernel Q) (hn : 2 ≤ n) :
    hellingerSq (seqLaw P) (seqLaw Q) ≤ 10 ^ 2 * Real.log n * condHellingerSum P Q := by sorry

end StatComplexityDM.HellingerChain
